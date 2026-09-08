/-
Copyright (c) 2023 Yaël Dillies, Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Zichen Wang
-/
module

public import Mathlib.Analysis.Normed.Affine.Convex

/-!
# Convex functions are continuous

This file proves that a convex function from a finite-dimensional real normed space to `ℝ` is
continuous.
-/

public section

open FiniteDimensional Metric Set List Bornology
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {C : Set E} {f : E → ℝ} {x₀ : E} {ε r r' M : ℝ}

/-
**ConvexOn.lipschitzOnWith_of_abs_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ConvexOn.lipschitzOnWith_of_abs_le (hf : ConvexOn Real (ball x₀ r) f) (hε 
: 0 < ε) (hM : forall a, dist a x₀ < r -> |f a| <= M) : LipschitzOnWith (2 * M /
 ε).toNNReal f (ball x₀ (r - ε))
参数：hf : ConvexOn Real (ball x₀ r) f；hε : 0 < ε；hM : forall a, dist a x₀ < r -> |
f a| <= M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Metric.ball_subset_ball`：ball_subset_ball (h : ε₁ <= ε₂) : ball x ε₁ sub
seteq ball x ε₂
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
（共 141 条，此处仅展示前 30 条）
-/
lemma ConvexOn.lipschitzOnWith_of_abs_le (hf : ConvexOn ℝ (ball x₀ r) f) (hε : 0 < ε)
    (hM : ∀ a, dist a x₀ < r → |f a| ≤ M) :
    LipschitzOnWith (2 * M / ε).toNNReal f (ball x₀ (r - ε)) := by
  set K := 2 * M / ε with hK
  have oneside {x y : E} (hx : x ∈ ball x₀ (r - ε)) (hy : y ∈ ball x₀ (r - ε)) :
      f x - f y ≤ K * ‖x - y‖ := by
    obtain rfl | hxy := eq_or_ne x y
    · simp
    have hx₀r : ball x₀ (r - ε) ⊆ ball x₀ r := ball_subset_ball <| by linarith
    have hx' : x ∈ ball x₀ r := hx₀r hx
    have hy' : y ∈ ball x₀ r := hx₀r hy
    let z := x + (ε / ‖x - y‖) • (x - y)
    replace hxy : 0 < ‖x - y‖ := by rwa [norm_sub_pos_iff]
    have hz : z ∈ ball x₀ r := mem_ball_iff_norm.2 <| by
      calc
        _ = ‖(x - x₀) + (ε / ‖x - y‖) • (x - y)‖ := by simp only [z, add_sub_right_comm]
        _ ≤ ‖x - x₀‖ + ‖(ε / ‖x - y‖) • (x - y)‖ := norm_add_le ..
        _ < r - ε + ε :=
          add_lt_add_of_lt_of_le (mem_ball_iff_norm.1 hx) <| by
            simp [norm_smul, abs_of_nonneg, hε.le, hxy.ne']
        _ = r := by simp
    let a := ε / (ε + ‖x - y‖)
    let b := ‖x - y‖ / (ε + ‖x - y‖)
    have hab : a + b = 1 := by simp [field, a, b]
    have hxyz : x = a • y + b • z := by
      calc
        x = a • x + b • x := by rw [Convex.combo_self hab]
        _ = a • y + b • z := by simp [z, a, b, smul_smul, hxy.ne', smul_sub]; abel
    rw [hK, mul_comm, ← mul_div_assoc, le_div_iff₀' hε]
    calc
      ε * (f x - f y) ≤ ‖x - y‖ * (f z - f x) := by
        have h := hf.2 hy' hz (by positivity) (by positivity) hab
        simp only [← hxyz, smul_eq_mul, a, b] at h
        field_simp at h
        linear_combination h
      _ ≤ _ := by
        rw [sub_eq_add_neg (f _), two_mul]
        gcongr
        · exact (le_abs_self _).trans <| hM _ hz
        · exact (neg_le_abs _).trans <| hM _ hx'
  refine .of_dist_le' fun x hx y hy ↦ ?_
  simp_rw [dist_eq_norm_sub, Real.norm_eq_abs, abs_sub_le_iff]
  exact ⟨oneside hx hy, norm_sub_rev x _ ▸ oneside hy hx⟩
/-
**ConcaveOn.lipschitzOnWith_of_abs_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ConcaveOn.lipschitzOnWith_of_abs_le (hf : ConcaveOn Real (ball x₀ r) f) (h
ε : 0 < ε) (hM : forall a, dist a x₀ < r -> |f a| <= M) : LipschitzOnWith (2 * M
 / ε).toNNReal f (ball x₀ (r - ε))
参数：hf : ConcaveOn Real (ball x₀ r) f；hε : 0 < ε；hM : forall a, dist a x₀ < r -> 
|f a| <= M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `ConvexOn.lipschitzOnWith_of_abs_le`：ConvexOn.lipschitzOnWith_of_abs_le (
hf : ConvexOn Real (ball x₀ r) f) (hε : 0 < ε) (hM : forall a, dist a x₀ < r -> 
|f a| <= M) : LipschitzO…
· 使用定理 `ConcaveOn.neg`：∀ {𝕜 : Type u_1} {E : Type u_2} {β : Type u_5} [inst : Se
miring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : AddCo
mmG…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (a : 
α), |(-a)| = |a|
-/
lemma ConcaveOn.lipschitzOnWith_of_abs_le (hf : ConcaveOn ℝ (ball x₀ r) f) (hε : 0 < ε)
    (hM : ∀ a, dist a x₀ < r → |f a| ≤ M) :
    LipschitzOnWith (2 * M / ε).toNNReal f (ball x₀ (r - ε)) := by
  simpa using hf.neg.lipschitzOnWith_of_abs_le hε <| by simpa using hM
/-
**ConvexOn.exists_lipschitzOnWith_of_isBounded** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ConvexOn.exists_lipschitzOnWith_of_isBounded (hf : ConvexOn Real (ball x₀ 
r) f) (hr : r' < r) (hf' : IsBounded (f '' ball x₀ r)) : exists K, LipschitzOnWi
th K f (ball x₀ r')
参数：hf : ConvexOn Real (ball x₀ r) f；hr : r' < r；hf' : IsBounded (f '' ball x₀ r)
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `Metric.isBounded_iff_subset_ball`：isBounded_iff_subset_ball (c : α) : Is
Bounded s ↔ exists r, s subseteq ball c r
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `ConvexOn.lipschitzOnWith_of_abs_le`：ConvexOn.lipschitzOnWith_of_abs_le (
hf : ConvexOn Real (ball x₀ r) f) (hε : 0 < ε) (hM : forall a, dist a x₀ < r -> 
|f a| <= M) : LipschitzO…
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
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma ConvexOn.exists_lipschitzOnWith_of_isBounded (hf : ConvexOn ℝ (ball x₀ r) f) (hr : r' < r)
    (hf' : IsBounded (f '' ball x₀ r)) : ∃ K, LipschitzOnWith K f (ball x₀ r') := by
  rw [isBounded_iff_subset_ball 0] at hf'
  simp only [Set.subset_def, mem_image, mem_ball, dist_zero_right, Real.norm_eq_abs,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hf'
  obtain ⟨M, hM⟩ := hf'
  rw [← sub_sub_cancel r r']
  exact ⟨_, hf.lipschitzOnWith_of_abs_le (sub_pos.2 hr) fun a ha ↦ (hM a ha).le⟩
/-
**ConcaveOn.exists_lipschitzOnWith_of_isBounded** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ConcaveOn.exists_lipschitzOnWith_of_isBounded (hf : ConcaveOn Real (ball x
₀ r) f) (hr : r' < r) (hf' : IsBounded (f '' ball x₀ r)) : exists K, LipschitzOn
With K f (ball x₀ r')
参数：hf : ConcaveOn Real (ball x₀ r) f；hr : r' < r；hf' : IsBounded (f '' ball x₀ r
)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Bornology.IsBounded.neg`：∀ {E : Type u_1} [inst : SeminormedAddGroup E] 
{s : Set E}, Bornology.IsBounded s → Bornology.IsBounded (-s)
· 使用引理 `ConvexOn.exists_lipschitzOnWith_of_isBounded`：ConvexOn.exists_lipschitzO
nWith_of_isBounded (hf : ConvexOn Real (ball x₀ r) f) (hr : r' < r) (hf' : IsBou
nded (f '' ball x₀ r)) : exists K,…
· 使用定理 `ConcaveOn.neg`：∀ {𝕜 : Type u_1} {E : Type u_2} {β : Type u_5} [inst : Se
miring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : AddCo
mmG…
-/
lemma ConcaveOn.exists_lipschitzOnWith_of_isBounded (hf : ConcaveOn ℝ (ball x₀ r) f) (hr : r' < r)
    (hf' : IsBounded (f '' ball x₀ r)) : ∃ K, LipschitzOnWith K f (ball x₀ r') := by
  replace hf' : IsBounded ((-f) '' ball x₀ r) := by convert! hf'.neg; ext; simp [neg_eq_iff_eq_neg]
  simpa using hf.neg.exists_lipschitzOnWith_of_isBounded hr hf'
/-
**ConvexOn.isBoundedUnder_abs** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ConvexOn.isBoundedUnder_abs (hf : ConvexOn Real C f) {x₀ : E} (hC : C in 𝓝
 x₀) : (𝓝 x₀).IsBoundedUnder (· <= ·) |f| ↔ (𝓝 x₀).IsBoundedUnder (· <= ·) f
参数：hf : ConvexOn Real C f；hC : C in 𝓝 x₀。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.IsBoundedUnder.mono_le`：∀ {α : Type u_1} {β : Type u_2} [inst : P
reorder β] {l : Filter α} {u v : α → β},   Filter.IsBoundedUnder (fun x1 x2 => x
1 ≤ x2) l u → v ≤ᶠ[…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.tendsto_nhds_nhds`：tendsto_nhds_nhds [PseudoMetricSpace β] {f : α
 -> β} {a b} : Tendsto f (𝓝 a) (𝓝 b) ↔ forall ε > 0, exists δ > 0, forall ⦃x : α
⦄, dist x a < …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `two_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 2 • a = a + a
· 使用定理 `dist_sub_eq_dist_add_right`：∀ {E : Type u_2} [inst : SeminormedAddCommGr
oup E] (a b c : E), dist a (b - c) = dist (a + c) b
· 使用定理 `dist_add_left`：∀ {M : Type u} [inst : PseudoMetricSpace M] [inst_1 : Add
 M] [IsIsometricVAdd M M] (a b c : M),   dist (a + b) (a + c) = dist b c
· 使用定理 `NormedAddGroup.to_isIsometricVAdd`：∀ {E : Type u_2} [inst : SeminormedAd
dGroup E], IsIsometricVAdd E E
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Filter.Tendsto.eventually_mem`：∀ {α : Type u_1} {β : Type u_2} {f : α → 
β} {l₁ : Filter α} {l₂ : Filter β} {s : Set β},   Filter.Tendsto f l₁ l₂ → s ∈ l
₂ → ∀ᶠ (x : α) in l…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
（共 76 条，此处仅展示前 30 条）
-/
lemma ConvexOn.isBoundedUnder_abs (hf : ConvexOn ℝ C f) {x₀ : E} (hC : C ∈ 𝓝 x₀) :
    (𝓝 x₀).IsBoundedUnder (· ≤ ·) |f| ↔ (𝓝 x₀).IsBoundedUnder (· ≤ ·) f := by
  refine ⟨fun h ↦ h.mono_le <| .of_forall fun x ↦ le_abs_self _, ?_⟩
  rintro ⟨r, hr⟩
  refine ⟨|r| + 2 * |f x₀|, ?_⟩
  have : (𝓝 x₀).Tendsto (fun y => 2 • x₀ - y) (𝓝 x₀) :=
    tendsto_nhds_nhds.2 (⟨·, ·, by simp [two_nsmul, dist_comm]⟩)
  simp only [Filter.eventually_map, Pi.abs_apply, abs_le'] at hr ⊢
  filter_upwards [this.eventually_mem hC, hC, hr, this.eventually hr] with y hx hx' hfr hfr'
  refine ⟨hfr.trans <| (le_abs_self _).trans <| by simp, ?_⟩
  rw [← sub_le_iff_le_add, neg_sub_comm, sub_le_iff_le_add', ← abs_two, ← abs_mul]
  calc
    -|2 * f x₀| ≤ 2 * f x₀ := neg_abs_le _
    _ ≤ f y + f (2 • x₀ - y) := by
      have := hf.2 hx' hx (by positivity) (by positivity) (add_halves _)
      simp only [one_div, ← Nat.cast_smul_eq_nsmul ℝ, Nat.cast_ofNat, smul_sub, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, inv_smul_smul₀, add_sub_cancel, smul_eq_mul] at this
      cancel_denoms at this
      rwa [← Nat.cast_two, Nat.cast_smul_eq_nsmul] at this
    _ ≤ f y + |r| := by gcongr; exact hfr'.trans (le_abs_self _)
/-
**ConcaveOn.isBoundedUnder_abs** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ConcaveOn.isBoundedUnder_abs (hf : ConcaveOn Real C f) {x₀ : E} (hC : C in
 𝓝 x₀) : (𝓝 x₀).IsBoundedUnder (· <= ·) |f| ↔ (𝓝 x₀).IsBoundedUnder (· >= ·) f
参数：hf : ConcaveOn Real C f；hC : C in 𝓝 x₀。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `abs_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (a : 
α), |(-a)| = |a|
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `ConvexOn.isBoundedUnder_abs`：ConvexOn.isBoundedUnder_abs (hf : ConvexOn 
Real C f) {x₀ : E} (hC : C in 𝓝 x₀) : (𝓝 x₀).IsBoundedUnder (· <= ·) |f| ↔ (𝓝 x₀
).IsBoundedUnder …
· 使用定理 `ConcaveOn.neg`：∀ {𝕜 : Type u_1} {E : Type u_2} {β : Type u_5} [inst : Se
miring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : AddCo
mmG…
-/
lemma ConcaveOn.isBoundedUnder_abs (hf : ConcaveOn ℝ C f) {x₀ : E} (hC : C ∈ 𝓝 x₀) :
    (𝓝 x₀).IsBoundedUnder (· ≤ ·) |f| ↔ (𝓝 x₀).IsBoundedUnder (· ≥ ·) f := by
  simpa [Pi.neg_def, Pi.abs_def] using hf.neg.isBoundedUnder_abs hC
/-
**ConvexOn.continuousOn_tfae** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ConvexOn.continuousOn_tfae (hC : IsOpen C) (hC' : C.Nonempty) (hf : Convex
On Real C f) : TFAE [ LocallyLipschitzOn C f, ContinuousOn f C, exists x₀ in C, 
ContinuousAt f x₀, exists x₀ in C, (𝓝 x₀).IsBoundedUnder (· <= ·) f, forall ⦃x₀⦄
, x₀ in C -> (𝓝 x₀).IsBoundedUnder (· <= ·) f, forall ⦃x₀⦄, x₀ in C -> (𝓝 x₀).Is
BoundedUnder (· <= ·) |f|]
参数：hC : IsOpen C；hC' : C.Nonempty；hf : ConvexOn Real C f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocallyLipschitzOn.continuousOn`：∀ {α : Type u} {β : Type v} [inst : Pse
udoEMetricSpace α] [inst_1 : PseudoEMetricSpace β] {f : α → β} {s : Set α},   Lo
callyLipschitzOn s f …
· 使用定理 `ContinuousOn.continuousAt`：ContinuousOn.continuousAt (h : ContinuousOn f
 s) (hx : s in 𝓝 x) : ContinuousAt f x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `eventually_le_nhds`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 :
 LinearOrder α] [ClosedIciTopology α] {a b : α},   a < b → ∀ᶠ (x : α) in nhds a,
 x ≤ b
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
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
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `ContinuousAt.fun_sub`：∀ {G : Type u_1} {X : Type u_3} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f 
g : X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousAt.fun_smul`：∀ {M : Type u_1} {X : Type u_2} {Y : Type u_3} [i
nst : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalS
pace Y] [in…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `ContinuousAt.fun_inv₀`：∀ {α : Type u_1} {G₀ : Type u_3} [inst : Zero G₀]
 [inst_1 : Inv G₀] [inst_2 : TopologicalSpace G₀] [ContinuousInv₀ G₀]   {f : α →
 G₀} {a : α…
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `instIsTopologicalDivisionRingReal`：IsTopologicalDivisionRing ℝ
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `continuousAt_const`：continuousAt_const : ContinuousAt (fun _ : X => y) x
· 使用定理 `continuousAt_id'`：continuousAt_id' (y) : ContinuousAt (fun x : X => x) y
· 使用定理 `Mathlib.Meta.NormNum.isNat_eq_false`：∀ {α : Type u_1} [inst : AddMonoidW
ithOne α] [CharZero α] {a b : α} {a' b' : ℕ},   Mathlib.Meta.NormNum.IsNat a a' 
→ Mathlib.Meta.NormNum.Is…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_sub`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HSub.hSub →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
（共 117 条，此处仅展示前 30 条）
-/
lemma ConvexOn.continuousOn_tfae (hC : IsOpen C) (hC' : C.Nonempty) (hf : ConvexOn ℝ C f) : TFAE [
    LocallyLipschitzOn C f,
    ContinuousOn f C,
    ∃ x₀ ∈ C, ContinuousAt f x₀,
    ∃ x₀ ∈ C, (𝓝 x₀).IsBoundedUnder (· ≤ ·) f,
    ∀ ⦃x₀⦄, x₀ ∈ C → (𝓝 x₀).IsBoundedUnder (· ≤ ·) f,
    ∀ ⦃x₀⦄, x₀ ∈ C → (𝓝 x₀).IsBoundedUnder (· ≤ ·) |f|] := by
  tfae_have 1 → 2 := LocallyLipschitzOn.continuousOn
  tfae_have 2 → 3 := by
    obtain ⟨x₀, hx₀⟩ := hC'
    exact fun h ↦ ⟨x₀, hx₀, h.continuousAt <| hC.mem_nhds hx₀⟩
  tfae_have 3 → 4
  | ⟨x₀, hx₀, h⟩ =>
    ⟨x₀, hx₀, f x₀ + 1, by simpa using! h.eventually (eventually_le_nhds (by simp))⟩
  tfae_have 4 → 5
  | ⟨x₀, hx₀, r, hr⟩, x, hx => by
    have : ∀ᶠ δ in 𝓝 (0 : ℝ), (1 - δ)⁻¹ • x - (δ / (1 - δ)) • x₀ ∈ C := by
      have h : ContinuousAt (fun δ : ℝ ↦ (1 - δ)⁻¹ • x - (δ / (1 - δ)) • x₀) 0 := by
        fun_prop (disch := norm_num)
      exact h (by simpa using! hC.mem_nhds hx)
    obtain ⟨δ, hδ₀, hy, hδ₁⟩ := (this.and <| eventually_lt_nhds zero_lt_one).exists_gt
    set y := (1 - δ)⁻¹ • x - (δ / (1 - δ)) • x₀
    refine ⟨max r (f y), ?_⟩
    simp only [Filter.eventually_map] at hr ⊢
    obtain ⟨ε, hε, hr⟩ := Metric.eventually_nhds_iff.1 <| hr.and (hC.eventually_mem hx₀)
    refine Metric.eventually_nhds_iff.2 ⟨ε * δ, by positivity, fun z hz ↦ ?_⟩
    have hx₀' : δ⁻¹ • (x - y) + y = x₀ := MulAction.injective₀ (sub_ne_zero.2 hδ₁.ne') <| by
      simp [y, smul_sub, smul_smul, hδ₀.ne', div_eq_mul_inv, sub_ne_zero.2 hδ₁.ne', mul_left_comm,
        sub_mul, sub_smul]
    let w := δ⁻¹ • (z - y) + y
    have hwyz : δ • w + (1 - δ) • y = z := by simp [w, hδ₀.ne', sub_smul]
    have hw : dist w x₀ < ε := by
      simpa [w, ← hx₀', dist_smul₀, abs_of_nonneg, hδ₀.le, inv_mul_lt_iff₀', hδ₀]
    calc
      f z ≤ max (f w) (f y) :=
        hf.le_max_of_mem_segment (hr hw).2 hy ⟨_, _, hδ₀.le, sub_nonneg.2 hδ₁.le, by simp, hwyz⟩
      _ ≤ max r (f y) := by gcongr; exact (hr hw).1
  tfae_have 6 ↔ 5 := forall₂_congr fun x₀ hx₀ ↦ hf.isBoundedUnder_abs (hC.mem_nhds hx₀)
  tfae_have 6 → 1
  | h, x, hx => by
    obtain ⟨r, hr⟩ := h hx
    obtain ⟨ε, hε, hεD⟩ := Metric.mem_nhds_iff.1 <| Filter.inter_mem (hC.mem_nhds hx) hr
    simp only [preimage_ofPred_eq, Pi.abs_apply, subset_inter_iff, hC.nhdsWithin_eq hx] at hεD ⊢
    obtain ⟨K, hK⟩ := exists_lipschitzOnWith_of_isBounded (hf.subset hεD.1 (convex_ball ..))
      (half_lt_self hε) <| isBounded_iff_forall_norm_le.2 ⟨r, by simpa using! hεD.2⟩
    exact ⟨K, _, ball_mem_nhds _ (by simpa), hK⟩
  tfae_finish
/-
**ConcaveOn.continuousOn_tfae** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ConcaveOn.continuousOn_tfae (hC : IsOpen C) (hC' : C.Nonempty) (hf : Conca
veOn Real C f) : TFAE [ LocallyLipschitzOn C f, ContinuousOn f C, exists x₀ in C
, ContinuousAt f x₀, exists x₀ in C, (𝓝 x₀).IsBoundedUnder (· >= ·) f, forall ⦃x
₀⦄, x₀ in C -> (𝓝 x₀).IsBoundedUnder (· >= ·) f, forall ⦃x₀⦄, x₀ in C -> (𝓝 x₀).
IsBoundedUnder (· <= ·) |f|]
参数：hC : IsOpen C；hC' : C.Nonempty；hf : ConcaveOn Real C f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ConvexOn.continuousOn_tfae`：ConvexOn.continuousOn_tfae (hC : IsOpen C) (
hC' : C.Nonempty) (hf : ConvexOn Real C f) : TFAE [ LocallyLipschitzOn C f, Cont
inuousOn f C, ex…
· 使用定理 `ConcaveOn.neg`：∀ {𝕜 : Type u_1} {E : Type u_2} {β : Type u_5} [inst : Se
miring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : AddCo
mmG…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.exists_congr`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} {q : β → 
Prop} (e : α ≃ β),   (∀ (a : α), p a ↔ q (e a)) → ((∃ a, p a) ↔ ∃ b, q b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Equiv.neg_apply`：∀ (G : Type u_14) [inst : InvolutiveNeg G], ⇑(Equiv.neg
 G) = Neg.neg
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `abs_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (a : 
α), |(-a)| = |a|
-/
lemma ConcaveOn.continuousOn_tfae (hC : IsOpen C) (hC' : C.Nonempty) (hf : ConcaveOn ℝ C f) : TFAE [
    LocallyLipschitzOn C f,
    ContinuousOn f C,
    ∃ x₀ ∈ C, ContinuousAt f x₀,
    ∃ x₀ ∈ C, (𝓝 x₀).IsBoundedUnder (· ≥ ·) f,
    ∀ ⦃x₀⦄, x₀ ∈ C → (𝓝 x₀).IsBoundedUnder (· ≥ ·) f,
    ∀ ⦃x₀⦄, x₀ ∈ C → (𝓝 x₀).IsBoundedUnder (· ≤ ·) |f|] := by
  have := hf.neg.continuousOn_tfae hC hC'
  simp only [locallyLipschitzOn_neg_iff, continuousOn_neg_iff, continuousAt_neg_iff, abs_neg]
    at this
  convert! this using 8 <;> exact (Equiv.neg ℝ).exists_congr (by simp)
/-
**ConvexOn.locallyLipschitzOn_iff_continuousOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ConvexOn.locallyLipschitzOn_iff_continuousOn (hC : IsOpen C) (hf : ConvexO
n Real C f) : LocallyLipschitzOn C f ↔ ContinuousOn f C
参数：hC : IsOpen C；hf : ConvexOn Real C f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用引理 `ConvexOn.continuousOn_tfae`：ConvexOn.continuousOn_tfae (hC : IsOpen C) (
hC' : C.Nonempty) (hf : ConvexOn Real C f) : TFAE [ LocallyLipschitzOn C f, Cont
inuousOn f C, ex…
-/
lemma ConvexOn.locallyLipschitzOn_iff_continuousOn (hC : IsOpen C) (hf : ConvexOn ℝ C f) :
    LocallyLipschitzOn C f ↔ ContinuousOn f C := by
  obtain rfl | hC' := C.eq_empty_or_nonempty
  · simp
  · exact (hf.continuousOn_tfae hC hC').out 0 1
/-
**ConcaveOn.locallyLipschitzOn_iff_continuousOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ConcaveOn.locallyLipschitzOn_iff_continuousOn (hC : IsOpen C) (hf : Concav
eOn Real C f) : LocallyLipschitzOn C f ↔ ContinuousOn f C
参数：hC : IsOpen C；hf : ConcaveOn Real C f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用引理 `ConvexOn.locallyLipschitzOn_iff_continuousOn`：ConvexOn.locallyLipschitzO
n_iff_continuousOn (hC : IsOpen C) (hf : ConvexOn Real C f) : LocallyLipschitzOn
 C f ↔ ContinuousOn f C
· 使用定理 `ConcaveOn.neg`：∀ {𝕜 : Type u_1} {E : Type u_2} {β : Type u_5} [inst : Se
miring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : AddCo
mmG…
-/
lemma ConcaveOn.locallyLipschitzOn_iff_continuousOn (hC : IsOpen C) (hf : ConcaveOn ℝ C f) :
    LocallyLipschitzOn C f ↔ ContinuousOn f C := by
  simpa using hf.neg.locallyLipschitzOn_iff_continuousOn hC

variable [FiniteDimensional ℝ E]
/-
**ConvexOn.locallyLipschitzOn** 是 Mathlib 中的一个定理，位于命名空间 `ConvexOn`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] 
{C : Set E} {f : E → ℝ}   [FiniteDimensional ℝ E], IsOpen C → ConvexOn ℝ C f → L
ocallyLipschitzOn C f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `exists_mem_interior_convexHull_affineBasis`：exists_mem_interior_convexHu
ll_affineBasis (hs : s in 𝓝 x) : exists b : AffineBasis (Fin (finrank Real E + 1
)) Real E, x in interior (convex…
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用引理 `ConvexOn.continuousOn_tfae`：ConvexOn.continuousOn_tfae (hC : IsOpen C) (
hC' : C.Nonempty) (hf : ConvexOn Real C f) : TFAE [ LocallyLipschitzOn C f, Cont
inuousOn f C, ex…
· 使用定理 `BddAbove.isBoundedUnder`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorde
r α] {f : Filter β} {u : β → α} {s : Set β},   s ∈ f → BddAbove (u '' s) → Filte
r.IsBoundedUn…
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `BddAbove.mono`：BddAbove.mono ⦃s t : Set α⦄ (h : s subseteq t) : BddAbove
 t -> BddAbove s
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用引理 `ConvexOn.bddAbove_convexHull`：ConvexOn.bddAbove_convexHull {s t : Set E}
 (hst : s subseteq t) (hf : ConvexOn 𝕜 t f) : BddAbove (f '' s) -> BddAbove (f '
' convexHull 𝕜 s)
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `subset_convexHull`：subset_convexHull : s subseteq convexHull 𝕜 s
· 使用定理 `Set.Finite.bddAbove`：∀ {α : Type u} [inst : Preorder α] [IsDirectedOrder
 α] [Nonempty α] {s : Set α}, s.Finite → BddAbove s
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
· 使用定理 `Set.finite_range`：finite_range (f : ι -> α) [Finite ι] : (range f).Finit
e
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
protected lemma ConvexOn.locallyLipschitzOn (hC : IsOpen C) (hf : ConvexOn ℝ C f) :
    LocallyLipschitzOn C f := by
  obtain rfl | ⟨x₀, hx₀⟩ := C.eq_empty_or_nonempty
  · simp
  · obtain ⟨b, hx₀b, hbC⟩ := exists_mem_interior_convexHull_affineBasis (hC.mem_nhds hx₀)
    refine ((hf.continuousOn_tfae hC ⟨x₀, hx₀⟩).out 3 0).mp ?_
    refine ⟨x₀, hx₀, BddAbove.isBoundedUnder (IsOpen.mem_nhds isOpen_interior hx₀b) ?_⟩
    exact (hf.bddAbove_convexHull ((subset_convexHull ..).trans hbC)
      ((finite_range _).image _).bddAbove).mono (by gcongr; exact interior_subset)
/-
**ConcaveOn.locallyLipschitzOn** 是 Mathlib 中的一个定理，位于命名空间 `ConcaveOn`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] 
{C : Set E} {f : E → ℝ}   [FiniteDimensional ℝ E], IsOpen C → ConcaveOn ℝ C f → 
LocallyLipschitzOn C f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexOn.locallyLipschitzOn`：∀ {E : Type u_1} [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] {C : Set E} {f : E → ℝ}   [FiniteDimensional ℝ E]
, IsOpen C → Conv…
· 使用定理 `ConcaveOn.neg`：∀ {𝕜 : Type u_1} {E : Type u_2} {β : Type u_5} [inst : Se
miring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : AddCo
mmG…
-/
protected lemma ConcaveOn.locallyLipschitzOn (hC : IsOpen C) (hf : ConcaveOn ℝ C f) :
    LocallyLipschitzOn C f := by simpa using hf.neg.locallyLipschitzOn hC
/-
**ConvexOn.continuousOn** 是 Mathlib 中的一个定理，位于命名空间 `ConvexOn`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] 
{C : Set E} {f : E → ℝ}   [FiniteDimensional ℝ E], IsOpen C → ConvexOn ℝ C f → C
ontinuousOn f C
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocallyLipschitzOn.continuousOn`：∀ {α : Type u} {β : Type v} [inst : Pse
udoEMetricSpace α] [inst_1 : PseudoEMetricSpace β] {f : α → β} {s : Set α},   Lo
callyLipschitzOn s f …
· 使用定理 `ConvexOn.locallyLipschitzOn`：∀ {E : Type u_1} [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] {C : Set E} {f : E → ℝ}   [FiniteDimensional ℝ E]
, IsOpen C → Conv…
-/
protected lemma ConvexOn.continuousOn (hC : IsOpen C) (hf : ConvexOn ℝ C f) :
    ContinuousOn f C := (hf.locallyLipschitzOn hC).continuousOn
/-
**ConcaveOn.continuousOn** 是 Mathlib 中的一个定理，位于命名空间 `ConcaveOn`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] 
{C : Set E} {f : E → ℝ}   [FiniteDimensional ℝ E], IsOpen C → ConcaveOn ℝ C f → 
ContinuousOn f C
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocallyLipschitzOn.continuousOn`：∀ {α : Type u} {β : Type v} [inst : Pse
udoEMetricSpace α] [inst_1 : PseudoEMetricSpace β] {f : α → β} {s : Set α},   Lo
callyLipschitzOn s f …
· 使用定理 `ConcaveOn.locallyLipschitzOn`：∀ {E : Type u_1} [inst : NormedAddCommGrou
p E] [inst_1 : NormedSpace ℝ E] {C : Set E} {f : E → ℝ}   [FiniteDimensional ℝ E
], IsOpen C → Conc…
-/
protected lemma ConcaveOn.continuousOn (hC : IsOpen C) (hf : ConcaveOn ℝ C f) :
    ContinuousOn f C := (hf.locallyLipschitzOn hC).continuousOn
/-
**ConvexOn.locallyLipschitzOn_interior** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ConvexOn.locallyLipschitzOn_interior (hf : ConvexOn Real C f) : LocallyLip
schitzOn (interior C) f
参数：hf : ConvexOn Real C f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexOn.locallyLipschitzOn`：∀ {E : Type u_1} [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] {C : Set E} {f : E → ℝ}   [FiniteDimensional ℝ E]
, IsOpen C → Conv…
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `ConvexOn.subset`：ConvexOn.subset {t : Set E} (hf : ConvexOn 𝕜 t f) (hst 
: s subseteq t) (hs : Convex 𝕜 s) : ConvexOn 𝕜 s f
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `Convex.interior`：∀ {𝕜 : Type u_2} {E : Type u_3} [inst : Field 𝕜] [inst_
1 : PartialOrder 𝕜] [inst_2 : AddCommGroup E]   [inst_3 : _root_.Module 𝕜 E] [in
st_4 …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma ConvexOn.locallyLipschitzOn_interior (hf : ConvexOn ℝ C f) :
    LocallyLipschitzOn (interior C) f :=
  (hf.subset interior_subset hf.1.interior).locallyLipschitzOn isOpen_interior
/-
**ConcaveOn.locallyLipschitzOn_interior** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ConcaveOn.locallyLipschitzOn_interior (hf : ConcaveOn Real C f) : LocallyL
ipschitzOn (interior C) f
参数：hf : ConcaveOn Real C f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConcaveOn.locallyLipschitzOn`：∀ {E : Type u_1} [inst : NormedAddCommGrou
p E] [inst_1 : NormedSpace ℝ E] {C : Set E} {f : E → ℝ}   [FiniteDimensional ℝ E
], IsOpen C → Conc…
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `ConcaveOn.subset`：ConcaveOn.subset {t : Set E} (hf : ConcaveOn 𝕜 t f) (h
st : s subseteq t) (hs : Convex 𝕜 s) : ConcaveOn 𝕜 s f
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `Convex.interior`：∀ {𝕜 : Type u_2} {E : Type u_3} [inst : Field 𝕜] [inst_
1 : PartialOrder 𝕜] [inst_2 : AddCommGroup E]   [inst_3 : _root_.Module 𝕜 E] [in
st_4 …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma ConcaveOn.locallyLipschitzOn_interior (hf : ConcaveOn ℝ C f) :
    LocallyLipschitzOn (interior C) f :=
  (hf.subset interior_subset hf.1.interior).locallyLipschitzOn isOpen_interior
/-
**ConvexOn.continuousOn_interior** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ConvexOn.continuousOn_interior (hf : ConvexOn Real C f) : ContinuousOn f (
interior C)
参数：hf : ConvexOn Real C f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocallyLipschitzOn.continuousOn`：∀ {α : Type u} {β : Type v} [inst : Pse
udoEMetricSpace α] [inst_1 : PseudoEMetricSpace β] {f : α → β} {s : Set α},   Lo
callyLipschitzOn s f …
· 使用引理 `ConvexOn.locallyLipschitzOn_interior`：ConvexOn.locallyLipschitzOn_interi
or (hf : ConvexOn Real C f) : LocallyLipschitzOn (interior C) f
-/
lemma ConvexOn.continuousOn_interior (hf : ConvexOn ℝ C f) : ContinuousOn f (interior C) :=
  hf.locallyLipschitzOn_interior.continuousOn
/-
**ConcaveOn.continuousOn_interior** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ConcaveOn.continuousOn_interior (hf : ConcaveOn Real C f) : ContinuousOn f
 (interior C)
参数：hf : ConcaveOn Real C f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocallyLipschitzOn.continuousOn`：∀ {α : Type u} {β : Type v} [inst : Pse
udoEMetricSpace α] [inst_1 : PseudoEMetricSpace β] {f : α → β} {s : Set α},   Lo
callyLipschitzOn s f …
· 使用引理 `ConcaveOn.locallyLipschitzOn_interior`：ConcaveOn.locallyLipschitzOn_inte
rior (hf : ConcaveOn Real C f) : LocallyLipschitzOn (interior C) f
-/
lemma ConcaveOn.continuousOn_interior (hf : ConcaveOn ℝ C f) : ContinuousOn f (interior C) :=
  hf.locallyLipschitzOn_interior.continuousOn
/-
**ConvexOn.locallyLipschitz** 是 Mathlib 中的一个定理，位于命名空间 `ConvexOn`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] 
{f : E → ℝ} [FiniteDimensional ℝ E],   ConvexOn ℝ Set.univ f → LocallyLipschitz 
f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `interior_univ`：interior_univ : interior (univ : Set X) = univ
· 使用引理 `ConvexOn.locallyLipschitzOn_interior`：ConvexOn.locallyLipschitzOn_interi
or (hf : ConvexOn Real C f) : LocallyLipschitzOn (interior C) f
-/
protected lemma ConvexOn.locallyLipschitz (hf : ConvexOn ℝ univ f) : LocallyLipschitz f := by
  simpa using hf.locallyLipschitzOn_interior
/-
**ConcaveOn.locallyLipschitz** 是 Mathlib 中的一个定理，位于命名空间 `ConcaveOn`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] 
{f : E → ℝ} [FiniteDimensional ℝ E],   ConcaveOn ℝ Set.univ f → LocallyLipschitz
 f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `interior_univ`：interior_univ : interior (univ : Set X) = univ
· 使用引理 `ConcaveOn.locallyLipschitzOn_interior`：ConcaveOn.locallyLipschitzOn_inte
rior (hf : ConcaveOn Real C f) : LocallyLipschitzOn (interior C) f
-/
protected lemma ConcaveOn.locallyLipschitz (hf : ConcaveOn ℝ univ f) : LocallyLipschitz f := by
  simpa using hf.locallyLipschitzOn_interior

-- Commented out since `intrinsicInterior` is not imported (but should be once these are proved)
-- proof_wanted ConvexOn.locallyLipschitzOn_intrinsicInterior (hf : ConvexOn ℝ C f) :
--     LocallyLipschitzOn (intrinsicInterior ℝ C) f

-- proof_wanted ConcaveOn.locallyLipschitzOn_intrinsicInterior (hf : ConcaveOn ℝ C f) :
--     LocallyLipschitzOn (intrinsicInterior ℝ C) f

-- proof_wanted ConvexOn.continuousOn_intrinsicInterior (hf : ConvexOn ℝ C f) :
--     ContinuousOn f (intrinsicInterior ℝ C)

-- proof_wanted ConcaveOn.continuousOn_intrinsicInterior (hf : ConcaveOn ℝ C f) :
--     ContinuousOn f (intrinsicInterior ℝ C)

section Intervals

/-
**ConvexOn.continuousOn_Ici** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ConvexOn.continuousOn_Ici {f : Real -> Real} {y : Real} (hf_cvx : ConvexOn
 Real (Ici y) f) (hf_cont : ContinuousWithinAt f (Ici y) y) : ContinuousOn f (Ic
i y)
参数：hf_cvx : ConvexOn Real (Ici y) f；hf_cont : ContinuousWithinAt f (Ici y) y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_lt_of_le`：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b
· 使用引理 `ConvexOn.continuousOn_interior`：ConvexOn.continuousOn_interior (hf : Con
vexOn Real C f) : ContinuousOn f (interior C)
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuousWithinAt_iff_continuousAt`：continuousWithinAt_iff_continuousAt
 (h : s in 𝓝 x) : ContinuousWithinAt f s x ↔ ContinuousAt f x
· 使用定理 `Ioi_mem_nhds`：Ioi_mem_nhds (h : a < b) : Ioi a in 𝓝 b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `interior_Ici'`：interior_Ici' {a : α} (ha : (Iio a).Nonempty) : interior 
(Ici a) = Ioi a
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
-/
lemma ConvexOn.continuousOn_Ici {f : ℝ → ℝ} {y : ℝ} (hf_cvx : ConvexOn ℝ (Ici y) f)
    (hf_cont : ContinuousWithinAt f (Ici y) y) :
    ContinuousOn f (Ici y) := by
  intro x hx
  rcases eq_or_lt_of_le (α := ℝ) hx with rfl | hxy
  · exact hf_cont
  · have h := hf_cvx.continuousOn_interior x
    simp only [nonempty_Iio, interior_Ici', mem_Ioi] at h
    rw [continuousWithinAt_iff_continuousAt (Ioi_mem_nhds hxy)] at h
    exact (h hxy).continuousWithinAt
/-
**ConcaveOn.continuousOn_Ici** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ConcaveOn.continuousOn_Ici {f : Real -> Real} {y : Real} (hf_cnv : Concave
On Real (Ici y) f) (hf_cont : ContinuousWithinAt f (Ici y) y) : ContinuousOn f (
Ici y)
参数：hf_cnv : ConcaveOn Real (Ici y) f；hf_cont : ContinuousWithinAt f (Ici y) y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用引理 `ConvexOn.continuousOn_Ici`：ConvexOn.continuousOn_Ici {f : Real -> Real} 
{y : Real} (hf_cvx : ConvexOn Real (Ici y) f) (hf_cont : ContinuousWithinAt f (I
ci y) y) : Cont…
· 使用定理 `ConcaveOn.neg`：∀ {𝕜 : Type u_1} {E : Type u_2} {β : Type u_5} [inst : Se
miring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : AddCo
mmG…
· 使用定理 `ContinuousWithinAt.neg`：∀ {G : Type u_1} {X : Type u_3} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace G] [inst_2 : Neg G]   [ContinuousNeg G] {
f : X → G} {…
-/
lemma ConcaveOn.continuousOn_Ici {f : ℝ → ℝ} {y : ℝ} (hf_cnv : ConcaveOn ℝ (Ici y) f)
    (hf_cont : ContinuousWithinAt f (Ici y) y) :
    ContinuousOn f (Ici y) := by
  simpa using hf_cnv.neg.continuousOn_Ici hf_cont.neg
/-
**ConvexOn.continuousOn_Iic** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ConvexOn.continuousOn_Iic {f : Real -> Real} {y : Real} (hf_cvx : ConvexOn
 Real (Iic y) f) (hf_cont : ContinuousWithinAt f (Iic y) y) : ContinuousOn f (Ii
c y)
参数：hf_cvx : ConvexOn Real (Iic y) f；hf_cont : ContinuousWithinAt f (Iic y) y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_lt_of_le`：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b
· 使用引理 `ConvexOn.continuousOn_interior`：ConvexOn.continuousOn_interior (hf : Con
vexOn Real C f) : ContinuousOn f (interior C)
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuousWithinAt_iff_continuousAt`：continuousWithinAt_iff_continuousAt
 (h : s in 𝓝 x) : ContinuousWithinAt f s x ↔ ContinuousAt f x
· 使用定理 `Iio_mem_nhds`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Linea
rOrder α] [ClosedIciTopology α] {a b : α},   b < a → Set.Iio a ∈ nhds b
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `interior_Iic'`：interior_Iic' {a : α} (ha : (Ioi a).Nonempty) : interior 
(Iic a) = Iio a
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
-/
lemma ConvexOn.continuousOn_Iic {f : ℝ → ℝ} {y : ℝ} (hf_cvx : ConvexOn ℝ (Iic y) f)
    (hf_cont : ContinuousWithinAt f (Iic y) y) :
    ContinuousOn f (Iic y) := by
  intro x hx
  rcases eq_or_lt_of_le (α := ℝ) hx with rfl | hxy
  · exact hf_cont
  · have h := hf_cvx.continuousOn_interior x
    simp only [nonempty_Ioi, interior_Iic', mem_Iio] at h
    rw [continuousWithinAt_iff_continuousAt (Iio_mem_nhds hxy)] at h
    exact (h hxy).continuousWithinAt
/-
**ConcaveOn.continuousOn_Iic** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ConcaveOn.continuousOn_Iic {f : Real -> Real} {y : Real} (hf_cnv : Concave
On Real (Iic y) f) (hf_cont : ContinuousWithinAt f (Iic y) y) : ContinuousOn f (
Iic y)
参数：hf_cnv : ConcaveOn Real (Iic y) f；hf_cont : ContinuousWithinAt f (Iic y) y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用引理 `ConvexOn.continuousOn_Iic`：ConvexOn.continuousOn_Iic {f : Real -> Real} 
{y : Real} (hf_cvx : ConvexOn Real (Iic y) f) (hf_cont : ContinuousWithinAt f (I
ic y) y) : Cont…
· 使用定理 `ConcaveOn.neg`：∀ {𝕜 : Type u_1} {E : Type u_2} {β : Type u_5} [inst : Se
miring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : AddCo
mmG…
· 使用定理 `ContinuousWithinAt.neg`：∀ {G : Type u_1} {X : Type u_3} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace G] [inst_2 : Neg G]   [ContinuousNeg G] {
f : X → G} {…
-/
lemma ConcaveOn.continuousOn_Iic {f : ℝ → ℝ} {y : ℝ} (hf_cnv : ConcaveOn ℝ (Iic y) f)
    (hf_cont : ContinuousWithinAt f (Iic y) y) :
    ContinuousOn f (Iic y) := by
  simpa using hf_cnv.neg.continuousOn_Iic hf_cont.neg
/-
**ConvexOn.continuousOn_Ioc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ConvexOn.continuousOn_Ioc {f : Real -> Real} {y z : Real} (hf_cvx : Convex
On Real (Ioc y z) f) (hf_cont : ContinuousWithinAt f (Iic z) z) : ContinuousOn f
 (Ioc y z)
参数：hf_cvx : ConvexOn Real (Ioc y z) f；hf_cont : ContinuousWithinAt f (Iic z) z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_lt_of_le`：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuousWithinAt_Ioc_iff_Iic`：continuousWithinAt_Ioc_iff_Iic (h : a < 
b) : ContinuousWithinAt f (Ioc a b) b ↔ ContinuousWithinAt f (Iic b) b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `ConvexOn.continuousOn_interior`：ConvexOn.continuousOn_interior (hf : Con
vexOn Real C f) : ContinuousOn f (interior C)
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `continuousWithinAt_iff_continuousAt`：continuousWithinAt_iff_continuousAt
 (h : s in 𝓝 x) : ContinuousWithinAt f s x ↔ ContinuousAt f x
· 使用定理 `Ioo_mem_nhds`：Ioo_mem_nhds {a b x : α} (ha : a < x) (hb : x < b) : Ioo a
 b in 𝓝 x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `interior_Ioc`：interior_Ioc [NoMaxOrder α] {a b : α} : interior (Ioc a b)
 = Ioo a b
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
lemma ConvexOn.continuousOn_Ioc {f : ℝ → ℝ} {y z : ℝ} (hf_cvx : ConvexOn ℝ (Ioc y z) f)
    (hf_cont : ContinuousWithinAt f (Iic z) z) :
    ContinuousOn f (Ioc y z) := by
  intro x hx
  rcases eq_or_lt_of_le (α := ℝ) hx.2 with rfl | hxz
  · rw [continuousWithinAt_Ioc_iff_Iic hx.1]
    exact hf_cont
  · have h := hf_cvx.continuousOn_interior x
    simp only [interior_Ioc, mem_Ioo, hx.1, hxz, and_self, forall_const] at h
    rw [continuousWithinAt_iff_continuousAt (Ioo_mem_nhds hx.1 hxz)] at h
    exact h.continuousWithinAt
/-
**ConcaveOn.continuousOn_Ioc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ConcaveOn.continuousOn_Ioc {f : Real -> Real} {y z : Real} (hf_cnv : Conca
veOn Real (Ioc y z) f) (hf_cont : ContinuousWithinAt f (Iic z) z) : ContinuousOn
 f (Ioc y z)
参数：hf_cnv : ConcaveOn Real (Ioc y z) f；hf_cont : ContinuousWithinAt f (Iic z) z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用引理 `ConvexOn.continuousOn_Ioc`：ConvexOn.continuousOn_Ioc {f : Real -> Real} 
{y z : Real} (hf_cvx : ConvexOn Real (Ioc y z) f) (hf_cont : ContinuousWithinAt 
f (Iic z) z) : …
· 使用定理 `ConcaveOn.neg`：∀ {𝕜 : Type u_1} {E : Type u_2} {β : Type u_5} [inst : Se
miring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : AddCo
mmG…
· 使用定理 `ContinuousWithinAt.neg`：∀ {G : Type u_1} {X : Type u_3} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace G] [inst_2 : Neg G]   [ContinuousNeg G] {
f : X → G} {…
-/
lemma ConcaveOn.continuousOn_Ioc {f : ℝ → ℝ} {y z : ℝ} (hf_cnv : ConcaveOn ℝ (Ioc y z) f)
    (hf_cont : ContinuousWithinAt f (Iic z) z) :
    ContinuousOn f (Ioc y z) := by
  simpa using hf_cnv.neg.continuousOn_Ioc hf_cont.neg
/-
**ConvexOn.continuousOn_Ico** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ConvexOn.continuousOn_Ico {f : Real -> Real} {y z : Real} (hf_cvx : Convex
On Real (Ico y z) f) (hf_cont : ContinuousWithinAt f (Ici y) y) : ContinuousOn f
 (Ico y z)
参数：hf_cvx : ConvexOn Real (Ico y z) f；hf_cont : ContinuousWithinAt f (Ici y) y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_lt_of_le`：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuousWithinAt_Ico_iff_Ici`：∀ {α : Type u} {β : Type v} [inst : Topo
logicalSpace α] [inst_1 : LinearOrder α] [ClosedIciTopology α]   [inst_3 : Topol
ogicalSpace β] {a b …
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `ConvexOn.continuousOn_interior`：ConvexOn.continuousOn_interior (hf : Con
vexOn Real C f) : ContinuousOn f (interior C)
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `continuousWithinAt_iff_continuousAt`：continuousWithinAt_iff_continuousAt
 (h : s in 𝓝 x) : ContinuousWithinAt f s x ↔ ContinuousAt f x
· 使用定理 `Ioo_mem_nhds`：Ioo_mem_nhds {a b x : α} (ha : a < x) (hb : x < b) : Ioo a
 b in 𝓝 x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `interior_Ico`：interior_Ico [NoMinOrder α] {a b : α} : interior (Ico a b)
 = Ioo a b
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
lemma ConvexOn.continuousOn_Ico {f : ℝ → ℝ} {y z : ℝ} (hf_cvx : ConvexOn ℝ (Ico y z) f)
    (hf_cont : ContinuousWithinAt f (Ici y) y) :
    ContinuousOn f (Ico y z) := by
  intro x hx
  rcases eq_or_lt_of_le (α := ℝ) hx.1 with rfl | hyx
  · rw [continuousWithinAt_Ico_iff_Ici hx.2]
    exact hf_cont
  · have h := hf_cvx.continuousOn_interior x
    simp only [interior_Ico, mem_Ioo, hyx, hx.2, and_self, forall_const] at h
    rw [continuousWithinAt_iff_continuousAt (Ioo_mem_nhds hyx hx.2)] at h
    exact h.continuousWithinAt
/-
**ConcaveOn.continuousOn_Ico** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ConcaveOn.continuousOn_Ico {f : Real -> Real} {y z : Real} (hf_cnv : Conca
veOn Real (Ico y z) f) (hf_cont : ContinuousWithinAt f (Ici y) y) : ContinuousOn
 f (Ico y z)
参数：hf_cnv : ConcaveOn Real (Ico y z) f；hf_cont : ContinuousWithinAt f (Ici y) y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用引理 `ConvexOn.continuousOn_Ico`：ConvexOn.continuousOn_Ico {f : Real -> Real} 
{y z : Real} (hf_cvx : ConvexOn Real (Ico y z) f) (hf_cont : ContinuousWithinAt 
f (Ici y) y) : …
· 使用定理 `ConcaveOn.neg`：∀ {𝕜 : Type u_1} {E : Type u_2} {β : Type u_5} [inst : Se
miring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : AddCo
mmG…
· 使用定理 `ContinuousWithinAt.neg`：∀ {G : Type u_1} {X : Type u_3} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace G] [inst_2 : Neg G]   [ContinuousNeg G] {
f : X → G} {…
-/
lemma ConcaveOn.continuousOn_Ico {f : ℝ → ℝ} {y z : ℝ} (hf_cnv : ConcaveOn ℝ (Ico y z) f)
    (hf_cont : ContinuousWithinAt f (Ici y) y) :
    ContinuousOn f (Ico y z) := by
  simpa using hf_cnv.neg.continuousOn_Ico hf_cont.neg
/-
**ConvexOn.continuousOn_Icc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ConvexOn.continuousOn_Icc {f : Real -> Real} {y z : Real} (hf_cvx : Convex
On Real (Icc y z) f) (hyz : y < z) (hfy : ContinuousWithinAt f (Ici y) y) (hfz :
 ContinuousWithinAt f (Iic z) z) : ContinuousOn f (Icc y z)
参数：hf_cvx : ConvexOn Real (Icc y z) f；hyz : y < z；hfy : ContinuousWithinAt f (Ic
i y) y；hfz : ContinuousWithinAt f (Iic z) z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ConvexOn.continuousOn_Ico`：ConvexOn.continuousOn_Ico {f : Real -> Real} 
{y z : Real} (hf_cvx : ConvexOn Real (Ico y z) f) (hf_cont : ContinuousWithinAt 
f (Ici y) y) : …
· 使用定理 `ConvexOn.subset`：ConvexOn.subset {t : Set E} (hf : ConvexOn 𝕜 t f) (hst 
: s subseteq t) (hs : Convex 𝕜 s) : ConvexOn 𝕜 s f
· 使用定理 `Set.Ico_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ico b a ⊆ Set.Icc b a
· 使用定理 `convex_Ico`：convex_Ico (r s : β) : Convex 𝕜 (Ico r s)
· 使用定理 `IsStrictOrderedModule.toPosSMulStrictMono`：∀ {α : Type u_1} {β : Type u_
2} {inst : SMul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero 
α}   {inst_4 : Zero β} [self : …
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用引理 `ConvexOn.continuousOn_Ioc`：ConvexOn.continuousOn_Ioc {f : Real -> Real} 
{y z : Real} (hf_cvx : ConvexOn Real (Ioc y z) f) (hf_cont : ContinuousWithinAt 
f (Iic z) z) : …
· 使用定理 `Set.Ioc_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc a b ⊆ Set.Icc a b
· 使用定理 `convex_Ioc`：convex_Ioc (r s : β) : Convex 𝕜 (Ioc r s)
· 使用定理 `eq_or_lt_of_le`：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ContinuousWithinAt.mono`：ContinuousWithinAt.mono (h : ContinuousWithinAt
 f t x) (hs : s subseteq t) : ContinuousWithinAt f s x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuousWithinAt_iff_continuousAt`：continuousWithinAt_iff_continuousAt
 (h : s in 𝓝 x) : ContinuousWithinAt f s x ↔ ContinuousAt f x
· 使用定理 `Ico_mem_nhds`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Linea
rOrder α] [OrderClosedTopology α] {a b x : α},   b < x → x < a → Set.Ico b a ∈ n
hd…
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
-/
lemma ConvexOn.continuousOn_Icc {f : ℝ → ℝ} {y z : ℝ} (hf_cvx : ConvexOn ℝ (Icc y z) f)
    (hyz : y < z)
    (hfy : ContinuousWithinAt f (Ici y) y) (hfz : ContinuousWithinAt f (Iic z) z) :
    ContinuousOn f (Icc y z) := by
  suffices ContinuousOn f (Ico y z) ∧ ContinuousOn f (Ioc y z) by
    intro x hx
    rcases eq_or_lt_of_le (α := ℝ) hx.1 with rfl | hyx
    · exact hfy.mono (by grind)
    rcases eq_or_lt_of_le (α := ℝ) hx.2 with rfl | hxz
    · exact hfz.mono (by grind)
    have hx := this.1 x (by grind)
    rw [continuousWithinAt_iff_continuousAt (Ico_mem_nhds hyx hxz)] at hx
    exact hx.continuousWithinAt
  refine ⟨ConvexOn.continuousOn_Ico ?_ hfy, ConvexOn.continuousOn_Ioc ?_ hfz⟩
  · exact hf_cvx.subset Ico_subset_Icc_self (convex_Ico y z)
  · exact hf_cvx.subset Ioc_subset_Icc_self (convex_Ioc y z)
/-
**ConcaveOn.continuousOn_Icc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ConcaveOn.continuousOn_Icc {f : Real -> Real} {y z : Real} (hf_cnv : Conca
veOn Real (Icc y z) f) (hyz : y < z) (hfy : ContinuousWithinAt f (Ici y) y) (hfz
 : ContinuousWithinAt f (Iic z) z) : ContinuousOn f (Icc y z)
参数：hf_cnv : ConcaveOn Real (Icc y z) f；hyz : y < z；hfy : ContinuousWithinAt f (I
ci y) y；hfz : ContinuousWithinAt f (Iic z) z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用引理 `ConvexOn.continuousOn_Icc`：ConvexOn.continuousOn_Icc {f : Real -> Real} 
{y z : Real} (hf_cvx : ConvexOn Real (Icc y z) f) (hyz : y < z) (hfy : Continuou
sWithinAt f (Ic…
· 使用定理 `ConcaveOn.neg`：∀ {𝕜 : Type u_1} {E : Type u_2} {β : Type u_5} [inst : Se
miring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : AddCo
mmG…
· 使用定理 `ContinuousWithinAt.neg`：∀ {G : Type u_1} {X : Type u_3} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace G] [inst_2 : Neg G]   [ContinuousNeg G] {
f : X → G} {…
-/
lemma ConcaveOn.continuousOn_Icc {f : ℝ → ℝ} {y z : ℝ} (hf_cnv : ConcaveOn ℝ (Icc y z) f)
    (hyz : y < z)
    (hfy : ContinuousWithinAt f (Ici y) y) (hfz : ContinuousWithinAt f (Iic z) z) :
    ContinuousOn f (Icc y z) := by
  simpa using hf_cnv.neg.continuousOn_Icc hyz hfy.neg hfz.neg

end Intervals

