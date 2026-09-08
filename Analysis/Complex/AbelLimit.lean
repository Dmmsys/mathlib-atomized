/-
Copyright (c) 2024 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Tactic.Peel
public import Mathlib.Tactic.Positivity

/-!
# Abel's limit theorem

If a real or complex power series for a function has radius of convergence 1 and the series is only
known to converge conditionally at 1, Abel's limit theorem gives the value at 1 as the limit of the
function at 1 from the left. "Left" for complex numbers means within a fixed cone opening to the
left with angle less than `π`.

## Main theorems

* `Complex.tendsto_tsum_powerSeries_nhdsWithin_stolzCone`:
  Abel's limit theorem for complex power series.
* `Real.tendsto_tsum_powerSeries_nhdsWithin_lt`: Abel's limit theorem for real power series.

## References

* https://planetmath.org/proofofabelslimittheorem
* https://en.wikipedia.org/wiki/Abel%27s_theorem
-/

@[expose] public section


open Filter Finset

open scoped Topology

namespace Complex

section StolzSet

open Real

/-- The Stolz set for a given `M`, roughly teardrop-shaped with the tip at 1 but tending to the
open unit disc as `M` tends to infinity. -/
/-
**Complex.stolzSet** 是 Mathlib 中的一个定义，位于命名空间 `Complex`。
形式化陈述：stolzSet (M : Real) : Set Complex
参数：M : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Stolz set for a given `M`, roughly teardrop-shaped with the tip at 1 but ten
ding to the
open unit disc as `M` tends to infinity.
-/
def stolzSet (M : ℝ) : Set ℂ := {z | ‖z‖ < 1 ∧ ‖1 - z‖ < M * (1 - ‖z‖)}

/-- The cone to the left of `1` with angle `2θ` such that `tan θ = s`. -/
/-
**Complex.stolzCone** 是 Mathlib 中的一个定义，位于命名空间 `Complex`。
形式化陈述：stolzCone (s : Real) : Set Complex
参数：s : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cone to the left of `1` with angle `2θ` such that `tan θ = s`.
-/
def stolzCone (s : ℝ) : Set ℂ := {z | |z.im| < s * (1 - z.re)}
/-
**Complex.stolzSet_empty** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：stolzSet_empty {M : Real} (hM : M <= 1) : stolzSet M = ∅
参数：hM : M <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.stolzSet.eq_1`：∀ (M : ℝ), Complex.stolzSet M = {z | ‖z‖ < 1 ∧ ‖1
 - z‖ < M * (1 - ‖z‖)}
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `Set.mem_empty_iff_false`：mem_empty_iff_false (x : α) : x in (∅ : Set α) 
↔ False
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `not_and`：∀ {a b : Prop}, ¬(a ∧ b) ↔ a → ¬b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, 0 < a - b ↔ b < a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `norm_sub_norm_le`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a 
b : E), ‖a‖ - ‖b‖ ≤ ‖a - b‖
-/
theorem stolzSet_empty {M : ℝ} (hM : M ≤ 1) : stolzSet M = ∅ := by
  ext z
  rw [stolzSet, Set.mem_ofPred, Set.mem_empty_iff_false, iff_false, not_and, not_lt, ← sub_pos]
  intro zn
  calc
    _ ≤ 1 * (1 - ‖z‖) := by gcongr
    _ = ‖(1 : ℂ)‖ - ‖z‖ := by rw [one_mul, norm_one]
    _ ≤ _ := norm_sub_norm_le _ _
/-
**Complex.nhdsWithin_lt_le_nhdsWithin_stolzSet** 是 Mathlib 中的一个定理，位于命名空间 `Comple
x`。
形式化陈述：nhdsWithin_lt_le_nhdsWithin_stolzSet {M : Real} (hM : 1 < M) : (𝓝[<] 1).ma
p ofReal <= 𝓝[stolzSet M] 1
参数：hM : 1 < M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.tendsto_id'`：tendsto_id' {x y : Filter α} : Tendsto id x y ↔ x <=
 y
· 使用定理 `Filter.tendsto_map'`：tendsto_map'_iff {f : β -> γ} {g : α -> β} {x : Fil
ter α} {y : Filter γ} : Tendsto f (map g x) y ↔ Tendsto (f ∘ g) x y
· 使用定理 `tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within`：tendsto_nhdsWit
hin_of_tendsto_nhds_of_eventually_within {a : α} {l : Filter β} {s : Set α} (f :
 β -> α) (h1 : Tendsto f l (𝓝 a)) (h2 : foral…
· 使用定理 `tendsto_nhdsWithin_of_tendsto_nhds`：tendsto_nhdsWithin_of_tendsto_nhds {
f : α -> β} {a : α} {s : Set α} {l : Filter β} (h : Tendsto f (𝓝 a) l) : Tendsto
 f (𝓝[s] a) l
· 使用定理 `Continuous.tendsto'`：Continuous.tendsto' (hf : Continuous f) (x : X) (y 
: Y) (h : f x = y) : Tendsto f (𝓝 x) (𝓝 y)
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `isOpen_Ioo`：isOpen_Ioo : IsOpen (Ioo a b)
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Complex.norm_real`：norm_real (r : Real) : ‖(r : Complex)‖ = ‖r‖
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, 0 < a - b ↔ b < a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
（共 36 条，此处仅展示前 30 条）
-/
theorem nhdsWithin_lt_le_nhdsWithin_stolzSet {M : ℝ} (hM : 1 < M) :
    (𝓝[<] 1).map ofReal ≤ 𝓝[stolzSet M] 1 := by
  rw [← tendsto_id']
  refine tendsto_map' <| tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within ofReal
    (tendsto_nhdsWithin_of_tendsto_nhds <| ofRealCLM.continuous.tendsto' 1 1 rfl) ?_
  simp only [eventually_iff, mem_nhdsWithin]
  refine ⟨Set.Ioo 0 2, isOpen_Ioo, by simp, fun x hx ↦ ?_⟩
  push _ ∈ _ at hx
  simp only [Set.mem_ofPred_eq, stolzSet, ← ofReal_one, ← ofReal_sub, norm_real,
    norm_of_nonneg hx.1.1.le, norm_of_nonneg <| (sub_pos.mpr hx.2).le]
  exact ⟨hx.2, lt_mul_left (sub_pos.mpr hx.2) hM⟩

-- An ugly technical lemma
/-
**Complex.stolzCone_subset_stolzSet_aux'** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma stolzCone_subset_stolzSet_aux' (s : ℝ) :
    ∃ M ε, 0 < M ∧ 0 < ε ∧ ∀ x y, 0 < x → x < ε → |y| < s * x →
      √(x ^ 2 + y ^ 2) < M * (1 - √((1 - x) ^ 2 + y ^ 2)) := by
  refine ⟨2 * √(1 + s ^ 2) + 1, 1 / (1 + s ^ 2), by positivity, by positivity,
    fun x y hx₀ hx₁ hy ↦ ?_⟩
  have H : √((1 - x) ^ 2 + y ^ 2) ≤ 1 - x / 2 := by
    calc √((1 - x) ^ 2 + y ^ 2)
      _ ≤ √((1 - x) ^ 2 + (s * x) ^ 2) := sqrt_le_sqrt <| by rw [← sq_abs y]; gcongr
      _ = √(1 - 2 * x + (1 + s ^ 2) * x * x) := by congr 1; ring
      _ ≤ √(1 - 2 * x + (1 + s ^ 2) * (1 / (1 + s ^ 2)) * x) := by gcongr
      _ = √(1 - x) := by congr 1; field
      _ ≤ 1 - x / 2 := by
        simp_rw [sub_eq_add_neg, ← neg_div]
        refine sqrt_one_add_le <| neg_le_neg_iff.mpr (hx₁.trans_le ?_).le
        rw [div_le_one (by positivity)]
        exact le_add_of_nonneg_right <| sq_nonneg s
  calc √(x ^ 2 + y ^ 2)
    _ ≤ √(x ^ 2 + (s * x) ^ 2) := by rw [← sq_abs y]; gcongr
    _ = √((1 + s ^ 2) * x ^ 2) := by congr; ring
    _ = √(1 + s ^ 2) * x := by rw [sqrt_mul' _ (sq_nonneg x), sqrt_sq hx₀.le]
    _ = 2 * √(1 + s ^ 2) * (x / 2) := by ring
    _ < (2 * √(1 + s ^ 2) + 1) * (x / 2) := by gcongr; exact lt_add_one _
    _ ≤ _ := by gcongr; exact le_sub_comm.mpr H
/-
**Complex.stolzCone_subset_stolzSet_aux** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：stolzCone_subset_stolzSet_aux {s : Real} (hs : 0 < s) : exists M ε, 0 < M 
∧ 0 < ε ∧ {z : Complex | 1 - ε < z.re} inter stolzCone s subseteq stolzSet M
参数：hs : 0 < s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用引理 `Mathlib.Tactic.Peel.and_imp_left_of_imp_imp`：and_imp_left_of_imp_imp {p 
q r : Prop} (h : r -> p -> q) : r ∧ p -> r ∧ q
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_pos_iff_of_pos_left`：mul_pos_iff_of_pos_left [PosMulStrictMono α] [P
osMulReflectLT α] (h : 0 < a) : 0 < a * b ↔ 0 < b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.sub_re`：sub_re (z w : Complex) : (z - w).re = z.re - w.re
· 使用定理 `Complex.one_re`：one_re : (1 : Complex).re = 1
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `Complex.stolzCone.eq_1`：∀ (s : ℝ), Complex.stolzCone s = {z | |z.im| < s
 * (1 - z.re)}
· 使用定理 `sub_lt_comm`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : LT α] [Add
LeftStrictMono α] {a b c : α}, a - b < c ↔ a - c < b
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用引理 `neg_sq`：neg_sq (a : R) : (-a) ^ 2 = a ^ 2
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, 0 < a - b ↔ b < a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
（共 37 条，此处仅展示前 30 条）
-/
lemma stolzCone_subset_stolzSet_aux {s : ℝ} (hs : 0 < s) :
    ∃ M ε, 0 < M ∧ 0 < ε ∧ {z : ℂ | 1 - ε < z.re} ∩ stolzCone s ⊆ stolzSet M := by
  peel stolzCone_subset_stolzSet_aux' s with M ε hM hε H
  rintro z ⟨hzl, hzr⟩
  rw [Set.mem_ofPred_eq, sub_lt_comm, ← one_re, ← sub_re] at hzl
  rw [stolzCone, Set.mem_ofPred_eq, ← one_re, ← sub_re] at hzr
  replace H :=
    H (1 - z).re z.im ((mul_pos_iff_of_pos_left hs).mp <| (abs_nonneg z.im).trans_lt hzr) hzl hzr
  have h : z.im ^ 2 = (1 - z).im ^ 2 := by
    simp only [sub_im, one_im, zero_sub, neg_sq]
  rw [h, ← norm_eq_sqrt_sq_add_sq, ← h, sub_re, one_re, sub_sub_cancel,
    ← norm_eq_sqrt_sq_add_sq] at H
  exact ⟨sub_pos.mp <| (mul_pos_iff_of_pos_left hM).mp <| (norm_nonneg _).trans_lt H, H⟩
/-
**Complex.nhdsWithin_stolzCone_le_nhdsWithin_stolzSet** 是 Mathlib 中的一个引理，位于命名空间 
`Complex`。
形式化陈述：nhdsWithin_stolzCone_le_nhdsWithin_stolzSet {s : Real} (hs : 0 < s) : exis
ts M, 𝓝[stolzCone s] 1 <= 𝓝[stolzSet M] 1
参数：hs : 0 < s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Complex.stolzCone_subset_stolzSet_aux`：stolzCone_subset_stolzSet_aux {s 
: Real} (hs : 0 < s) : exists M ε, 0 < M ∧ 0 < ε ∧ {z : Complex | 1 - ε < z.re} 
inter stolzCone s subseteq …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsWithin_le_iff`：nhdsWithin_le_iff {s t : Set α} {x : α} : 𝓝[s] x <= 𝓝
[t] x ↔ t in 𝓝[s] x
· 使用定理 `mem_nhdsWithin`：mem_nhdsWithin {t : Set α} {a : α} {s : Set α} : t in 𝓝[
s] a ↔ exists u, IsOpen u ∧ a in u ∧ u inter s subseteq t
· 使用定理 `isOpen_lt`：isOpen_lt [TopologicalSpace β] {f g : β -> α} (hf : Continuou
s f) (hg : Continuous g) : IsOpen { b | f b < g b }
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `Complex.continuous_re`：Continuous Complex.re
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma nhdsWithin_stolzCone_le_nhdsWithin_stolzSet {s : ℝ} (hs : 0 < s) :
    ∃ M, 𝓝[stolzCone s] 1 ≤ 𝓝[stolzSet M] 1 := by
  obtain ⟨M, ε, _, hε, H⟩ := stolzCone_subset_stolzSet_aux hs
  use M
  rw [nhdsWithin_le_iff, mem_nhdsWithin]
  refine ⟨{w | 1 - ε < w.re}, isOpen_lt continuous_const continuous_re, ?_, H⟩
  simp only [Set.mem_ofPred_eq, one_re, sub_lt_self_iff, hε]

end StolzSet

variable {f : ℕ → ℂ} {l : ℂ}

/-- Auxiliary lemma for Abel's limit theorem. The difference between the sum `l` at 1 and the
power series's value at a point `z` away from 1 can be rewritten as `1 - z` times a power series
whose coefficients are tail sums of `l`. -/
/-
**Complex.abel_aux** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：abel_aux (h : Tendsto (fun n => ∑ i in range n, f i) atTop (𝓝 l)) {z : Com
plex} (hz : ‖z‖ < 1) : Tendsto (fun n => (1 - z) * ∑ i in range n, (l - ∑ j in r
ange (i + 1), f j) * z ^ i) atTop (𝓝 (l - ∑' n, f n * z ^ n))
参数：h : Tendsto (fun n => ∑ i in range n, f i) atTop (𝓝 l)；hz : ‖z‖ < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.sub`：∀ {G : Type u_1} {α : Type u_2} [inst : TopologicalS
pace G] [inst_1 : Sub G] [ContinuousSub G] {f g : α → G}   {l : Filter α} {a b :
 G},   F…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `HasSum.tendsto_sum_nat`：∀ {M : Type u_1} [inst : AddCommMonoid M] [inst_
1 : TopologicalSpace M] {m : M} {f : ℕ → M},   HasSum f m → Filter.Tendsto (fun 
n => ∑ i ∈ F…
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
· 使用定理 `summable_powerSeries_of_norm_lt_one`：summable_powerSeries_of_norm_lt_one
 {z : α} (h : CauchySeq fun n => ∑ i in range n, f i) (hz : ‖z‖ < 1) : Summable 
fun n => f n * z ^ n
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `Filter.Tendsto.cauchySeq`：Filter.Tendsto.cauchySeq [SemilatticeSup β] [N
onempty β] {f : β -> α} {x} (hx : Tendsto f atTop (𝓝 x)) : CauchySeq f
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Filter.Tendsto.mul`：Filter.Tendsto.mul {α : Type*} {f g : α -> M} {x : F
ilter α} {a b : M} (hf : Tendsto f x (𝓝 a)) (hg : Tendsto g x (𝓝 b)) : Tendsto (
fun x =>…
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Filter.Tendsto.neg`：∀ {G : Type u_1} {α : Type u_2} [inst : TopologicalS
pace G] [inst_1 : Neg G] [ContinuousNeg G] {f : α → G}   {l : Filter α} {y : G},
 Filter.…
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendsto_sub_nhds_zero_iff`：∀ {G : Type w} [inst : AddGroup G] [inst_1 : 
TopologicalSpace G] [IsTopologicalAddGroup G] {α : Type u_1} {l : Filter α}   {x
 : G} {u : α → …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `geom_sum_eq`：geom_sum_eq (h : x != 1) (n : Nat) : ∑ i in range n, x ^ i 
= (x ^ n - 1) / (x - 1)
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
（共 66 条，此处仅展示前 30 条）

--- 原说明 ---
Auxiliary lemma for Abel's limit theorem. The difference between the sum `l` at 
1 and the
power series's value at a point `z` away from 1 can be rewritten as `1 - z` time
s a power series
whose coefficients are tail sums of `l`.
-/
lemma abel_aux (h : Tendsto (fun n ↦ ∑ i ∈ range n, f i) atTop (𝓝 l)) {z : ℂ} (hz : ‖z‖ < 1) :
    Tendsto (fun n ↦ (1 - z) * ∑ i ∈ range n, (l - ∑ j ∈ range (i + 1), f j) * z ^ i)
      atTop (𝓝 (l - ∑' n, f n * z ^ n)) := by
  let s := fun n ↦ ∑ i ∈ range n, f i
  have k := h.sub (summable_powerSeries_of_norm_lt_one h.cauchySeq hz).hasSum.tendsto_sum_nat
  simp_rw [← sum_sub_distrib, ← mul_one_sub, ← geom_sum_mul_neg, ← mul_assoc, ← sum_mul,
    mul_comm, mul_sum _ _ (f _), range_eq_Ico, ← sum_Ico_Ico_comm', ← range_eq_Ico,
    ← sum_mul] at k
  conv at k =>
    enter [1, n]
    rw [sum_congr (g := fun j ↦ (∑ k ∈ range n, f k - ∑ k ∈ range (j + 1), f k) * z ^ j)
      rfl (fun j hj ↦ by congr 1; exact sum_Ico_eq_sub _ (mem_range.mp hj))]
  suffices Tendsto (fun n ↦ (l - s n) * ∑ i ∈ range n, z ^ i) atTop (𝓝 0) by
    simp_rw [mul_sum] at this
    replace this := (this.const_mul (1 - z)).add k
    conv at this =>
      enter [1, n]
      rw [← mul_add, ← sum_add_distrib]
      enter [2, 2, i]
      rw [← add_mul, sub_add_sub_cancel]
    rwa [mul_zero, zero_add] at this
  rw [← zero_mul (-1 / (z - 1))]
  apply Tendsto.mul
  · simpa only [neg_zero, neg_sub] using (tendsto_sub_nhds_zero_iff.mpr h).neg
  · conv =>
      enter [1, n]
      rw [geom_sum_eq (by contrapose! hz; simp [hz]), sub_div, sub_eq_add_neg, ← neg_div]
    rw [← zero_add (-1 / (z - 1)), ← zero_div (z - 1)]
    apply Tendsto.add (Tendsto.div_const (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hz) (z - 1))
    simp only [zero_div, zero_add, tendsto_const_nhds_iff]

/-- **Abel's limit theorem**. Given a power series converging at 1, the corresponding function
is continuous at 1 when approaching 1 within a fixed Stolz set. -/
/-
**Complex.tendsto_tsum_powerSeries_nhdsWithin_stolzSet** 是 Mathlib 中的一个定理，位于命名空间
 `Complex`。
形式化陈述：tendsto_tsum_powerSeries_nhdsWithin_stolzSet (h : Tendsto (fun n => ∑ i in
 range n, f i) atTop (𝓝 l)) {M : Real} : Tendsto (fun z => ∑' n, f n * z ^ n) (𝓝
[stolzSet M] 1) (𝓝 l)
参数：h : Tendsto (fun n => ∑ i in range n, f i) atTop (𝓝 l)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.stolzSet_empty`：stolzSet_empty {M : Real} (hM : M <= 1) : stolzS
et M = ∅
· 使用定理 `nhdsWithin_empty`：nhdsWithin_empty (a : α) : 𝓝[∅] a = ⊥
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.tendsto_atTop`：tendsto_atTop [Nonempty β] [SemilatticeSup β] {u :
 β -> α} {a : α} : Tendsto u atTop (𝓝 a) ↔ forall ε > 0, exists N, forall n >= N
, dist (u …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Metric.tendsto_nhdsWithin_nhds`：tendsto_nhdsWithin_nhds [PseudoMetricSpa
ce β] {f : α -> β} {a b} : Tendsto f (𝓝[s] a) (𝓝 b) ↔ forall ε > 0, exists δ > 0
, forall ⦃x : α⦄, x …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Right.add_pos_of_nonneg_of_pos`：∀ {α : Type u_1} [inst : AddZeroClass α]
 [inst_1 : Preorder α] [AddRightMono α] {a b : α}, 0 ≤ a → 0 < b → 0 < a + b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Finset.sum_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s
, 0 ≤ f…
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
（共 158 条，此处仅展示前 30 条）

--- 原说明 ---
**Abel's limit theorem**. Given a power series converging at 1, the correspondin
g function
is continuous at 1 when approaching 1 within a fixed Stolz set.
-/
theorem tendsto_tsum_powerSeries_nhdsWithin_stolzSet
    (h : Tendsto (fun n ↦ ∑ i ∈ range n, f i) atTop (𝓝 l)) {M : ℝ} :
    Tendsto (fun z ↦ ∑' n, f n * z ^ n) (𝓝[stolzSet M] 1) (𝓝 l) := by
  -- If `M ≤ 1` the Stolz set is empty and the statement is trivial
  rcases le_or_gt M 1 with hM | hM
  · simp_rw [stolzSet_empty hM, nhdsWithin_empty, tendsto_bot]
  -- Abbreviations
  let s := fun n ↦ ∑ i ∈ range n, f i
  let g := fun z ↦ ∑' n, f n * z ^ n
  have hm := Metric.tendsto_atTop.mp h
  rw [Metric.tendsto_nhdsWithin_nhds]
  simp only [dist_eq_norm] at hm ⊢
  -- Introduce the "challenge" `ε`
  intro ε εpos
  -- First bound, handles the tail
  obtain ⟨B₁, hB₁⟩ := hm (ε / 4 / M) (by positivity)
  -- Second bound, handles the head
  let F := ∑ i ∈ range B₁, ‖l - s (i + 1)‖
  use ε / 4 / (F + 1), by positivity
  intro z ⟨zn, zm⟩ zd
  have p := abel_aux h zn
  simp_rw [Metric.tendsto_atTop, dist_eq_norm, norm_sub_rev] at p
  -- Third bound, regarding the distance between `l - g z` and the rearranged sum
  obtain ⟨B₂, hB₂⟩ := p (ε / 2) (by positivity)
  clear hm p
  replace hB₂ := hB₂ (max B₁ B₂) (by simp)
  suffices ‖(1 - z) * ∑ i ∈ range (max B₁ B₂), (l - s (i + 1)) * z ^ i‖ < ε / 2 by
    calc
      _ = ‖l - g z‖ := by rw [norm_sub_rev]
      _ = ‖l - g z - (1 - z) * ∑ i ∈ range (max B₁ B₂), (l - s (i + 1)) * z ^ i +
          (1 - z) * ∑ i ∈ range (max B₁ B₂), (l - s (i + 1)) * z ^ i‖ := by rw [sub_add_cancel _]
      _ ≤ ‖l - g z - (1 - z) * ∑ i ∈ range (max B₁ B₂), (l - s (i + 1)) * z ^ i‖ +
          ‖(1 - z) * ∑ i ∈ range (max B₁ B₂), (l - s (i + 1)) * z ^ i‖ := norm_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add hB₂ this
      _ = _ := add_halves ε
  -- We break the rearranged sum along `B₁`
  calc
    _ = ‖(1 - z) * ∑ i ∈ range B₁, (l - s (i + 1)) * z ^ i +
        (1 - z) * ∑ i ∈ Ico B₁ (max B₁ B₂), (l - s (i + 1)) * z ^ i‖ := by
      rw [← mul_add, sum_range_add_sum_Ico _ (le_max_left B₁ B₂)]
    _ ≤ ‖(1 - z) * ∑ i ∈ range B₁, (l - s (i + 1)) * z ^ i‖ +
        ‖(1 - z) * ∑ i ∈ Ico B₁ (max B₁ B₂), (l - s (i + 1)) * z ^ i‖ := norm_add_le _ _
    _ = ‖1 - z‖ * ‖∑ i ∈ range B₁, (l - s (i + 1)) * z ^ i‖ +
        ‖1 - z‖ * ‖∑ i ∈ Ico B₁ (max B₁ B₂), (l - s (i + 1)) * z ^ i‖ := by
      rw [norm_mul, norm_mul]
    _ ≤ ‖1 - z‖ * ∑ i ∈ range B₁, ‖l - s (i + 1)‖ * ‖z‖ ^ i +
        ‖1 - z‖ * ∑ i ∈ Ico B₁ (max B₁ B₂), ‖l - s (i + 1)‖ * ‖z‖ ^ i := by
      gcongr <;> simp_rw [← norm_pow, ← norm_mul, norm_sum_le]
  -- then prove that the two pieces are each less than `ε / 4`
  have S₁ : ‖1 - z‖ * ∑ i ∈ range B₁, ‖l - s (i + 1)‖ * ‖z‖ ^ i < ε / 4 :=
    calc
      _ ≤ ‖1 - z‖ * ∑ i ∈ range B₁, ‖l - s (i + 1)‖ := by
        gcongr; nth_rw 3 [← mul_one ‖_‖]
        gcongr; exact pow_le_one₀ (norm_nonneg _) zn.le
      _ ≤ ‖1 - z‖ * (F + 1) := by gcongr; linarith only
      _ < _ := by rwa [norm_sub_rev, lt_div_iff₀ (by positivity)] at zd
  have S₂ : ‖1 - z‖ * ∑ i ∈ Ico B₁ (max B₁ B₂), ‖l - s (i + 1)‖ * ‖z‖ ^ i < ε / 4 :=
    calc
      _ ≤ ‖1 - z‖ * ∑ i ∈ Ico B₁ (max B₁ B₂), ε / 4 / M * ‖z‖ ^ i := by
        gcongr with i hi
        have := hB₁ (i + 1) (by linarith only [(mem_Ico.mp hi).1])
        rw [norm_sub_rev] at this
        exact this.le
      _ = ‖1 - z‖ * (ε / 4 / M) * ∑ i ∈ Ico B₁ (max B₁ B₂), ‖z‖ ^ i := by
        rw [← mul_sum, ← mul_assoc]
      _ ≤ ‖1 - z‖ * (ε / 4 / M) * ∑' i, ‖z‖ ^ i := by
        gcongr
        exact Summable.sum_le_tsum _ (fun _ _ ↦ by positivity)
          (summable_geometric_of_lt_one (by positivity) zn)
      _ = ‖1 - z‖ * (ε / 4 / M) / (1 - ‖z‖) := by
        rw [tsum_geometric_of_lt_one (by positivity) zn, ← div_eq_mul_inv]
      _ < M * (1 - ‖z‖) * (ε / 4 / M) / (1 - ‖z‖) := by gcongr
      _ = _ := by
        rw [← mul_rotate, mul_div_cancel_right₀ _ (by linarith only [zn]),
          div_mul_cancel₀ _ (by linarith only [hM])]
  convert! add_lt_add S₁ S₂ using 1
  linarith only

/-- **Abel's limit theorem**. Given a power series converging at 1, the corresponding function
is continuous at 1 when approaching 1 within any fixed Stolz cone. -/
/-
**Complex.tendsto_tsum_powerSeries_nhdsWithin_stolzCone** 是 Mathlib 中的一个定理，位于命名空
间 `Complex`。
形式化陈述：tendsto_tsum_powerSeries_nhdsWithin_stolzCone (h : Tendsto (fun n => ∑ i i
n range n, f i) atTop (𝓝 l)) {s : Real} (hs : 0 < s) : Tendsto (fun z => ∑' n, f
 n * z ^ n) (𝓝[stolzCone s] 1) (𝓝 l)
参数：h : Tendsto (fun n => ∑ i in range n, f i) atTop (𝓝 l)；hs : 0 < s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用引理 `Complex.nhdsWithin_stolzCone_le_nhdsWithin_stolzSet`：nhdsWithin_stolzCon
e_le_nhdsWithin_stolzSet {s : Real} (hs : 0 < s) : exists M, 𝓝[stolzCone s] 1 <=
 𝓝[stolzSet M] 1
· 使用定理 `Complex.tendsto_tsum_powerSeries_nhdsWithin_stolzSet`：tendsto_tsum_power
Series_nhdsWithin_stolzSet (h : Tendsto (fun n => ∑ i in range n, f i) atTop (𝓝 
l)) {M : Real} : Tendsto (fun z => ∑' n, f…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose

--- 原说明 ---
**Abel's limit theorem**. Given a power series converging at 1, the correspondin
g function
is continuous at 1 when approaching 1 within any fixed Stolz cone.
-/
theorem tendsto_tsum_powerSeries_nhdsWithin_stolzCone
    (h : Tendsto (fun n ↦ ∑ i ∈ range n, f i) atTop (𝓝 l)) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun z ↦ ∑' n, f n * z ^ n) (𝓝[stolzCone s] 1) (𝓝 l) :=
  (tendsto_tsum_powerSeries_nhdsWithin_stolzSet h).mono_left
    (nhdsWithin_stolzCone_le_nhdsWithin_stolzSet hs).choose_spec
/-
**Complex.tendsto_tsum_powerSeries_nhdsWithin_lt** 是 Mathlib 中的一个定理，位于命名空间 `Comp
lex`。
形式化陈述：tendsto_tsum_powerSeries_nhdsWithin_lt (h : Tendsto (fun n => ∑ i in range
 n, f i) atTop (𝓝 l)) : Tendsto (fun z => ∑' n, f n * z ^ n) ((𝓝[<] 1).map ofRea
l) (𝓝 l)
参数：h : Tendsto (fun n => ∑ i in range n, f i) atTop (𝓝 l)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Complex.tendsto_tsum_powerSeries_nhdsWithin_stolzSet`：tendsto_tsum_power
Series_nhdsWithin_stolzSet (h : Tendsto (fun n => ∑ i in range n, f i) atTop (𝓝 
l)) {M : Real} : Tendsto (fun z => ∑' n, f…
· 使用定理 `Complex.nhdsWithin_lt_le_nhdsWithin_stolzSet`：nhdsWithin_lt_le_nhdsWithi
n_stolzSet {M : Real} (hM : 1 < M) : (𝓝[<] 1).map ofReal <= 𝓝[stolzSet M] 1
· 使用引理 `one_lt_two`：one_lt_two [AddLeftStrictMono α] : (1 : α) < 2
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem tendsto_tsum_powerSeries_nhdsWithin_lt
    (h : Tendsto (fun n ↦ ∑ i ∈ range n, f i) atTop (𝓝 l)) :
    Tendsto (fun z ↦ ∑' n, f n * z ^ n) ((𝓝[<] 1).map ofReal) (𝓝 l) :=
  (tendsto_tsum_powerSeries_nhdsWithin_stolzSet (M := 2) h).mono_left
    (nhdsWithin_lt_le_nhdsWithin_stolzSet one_lt_two)

end Complex

namespace Real

open Complex

variable {f : ℕ → ℝ} {l : ℝ}

/-- **Abel's limit theorem**. Given a real power series converging at 1, the corresponding function
is continuous at 1 when approaching 1 from the left. -/
/-
**Real.tendsto_tsum_powerSeries_nhdsWithin_lt** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：tendsto_tsum_powerSeries_nhdsWithin_lt (h : Tendsto (fun n => ∑ i in range
 n, f i) atTop (𝓝 l)) : Tendsto (fun x => ∑' n, f n * x ^ n) (𝓝[<] 1) (𝓝 l)
参数：h : Tendsto (fun n => ∑ i in range n, f i) atTop (𝓝 l)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
· 使用定理 `Filter.Tendsto.mono_right`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
x : Filter α} {y z : Filter β},   Filter.Tendsto f x y → y ≤ z → Filter.Tendsto 
f x z
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.tendsto_map`：tendsto_map {f : α -> β} {x : Filter α} : Tendsto f 
x (map f x)
· 使用定理 `Complex.tendsto_tsum_powerSeries_nhdsWithin_lt`：tendsto_tsum_powerSeries
_nhdsWithin_lt (h : Tendsto (fun n => ∑ i in range n, f i) atTop (𝓝 l)) : Tendst
o (fun z => ∑' n, f n * z ^ n) ((𝓝[<…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Complex.ofReal_sum`：ofReal_sum (f : α -> Real) : ((∑ i in s, f i : Real)
 : Complex) = ∑ i in s, (f i : Complex)
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `Metric.tendsto_nhdsWithin_nhds`：tendsto_nhdsWithin_nhds [PseudoMetricSpa
ce β] {f : α -> β} {a b} : Tendsto f (𝓝[s] a) (𝓝 b) ↔ forall ε > 0, exists δ > 0
, forall ⦃x : α⦄, x …
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Complex.norm_real`：norm_real (r : Real) : ‖(r : Complex)‖ = ‖r‖
· 使用定理 `Filter.tendsto_map'_iff`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
{f : β → γ} {g : α → β} {x : Filter α} {y : Filter γ},   Filter.Tendsto f (Filte
r.map g x) y …

--- 原说明 ---
**Abel's limit theorem**. Given a real power series converging at 1, the corresp
onding function
is continuous at 1 when approaching 1 from the left.
-/
theorem tendsto_tsum_powerSeries_nhdsWithin_lt
    (h : Tendsto (fun n ↦ ∑ i ∈ range n, f i) atTop (𝓝 l)) :
    Tendsto (fun x ↦ ∑' n, f n * x ^ n) (𝓝[<] 1) (𝓝 l) := by
  have m : (𝓝 l).map ofReal ≤ 𝓝 ↑l := ofRealCLM.continuous.tendsto l
  replace h := (tendsto_map.comp h).mono_right m
  rw [Function.comp_def] at h
  push_cast at h
  replace h := Complex.tendsto_tsum_powerSeries_nhdsWithin_lt h
  rw [tendsto_map'_iff] at h
  rw [Metric.tendsto_nhdsWithin_nhds] at h ⊢
  convert! h
  simp_rw [Function.comp_apply, dist_eq_norm]
  norm_cast

end Real

