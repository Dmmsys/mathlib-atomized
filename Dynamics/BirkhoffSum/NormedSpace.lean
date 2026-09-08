/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Dynamics.BirkhoffSum.Average

/-!
# Birkhoff average in a normed space

In this file we prove some lemmas about the Birkhoff average (`birkhoffAverage`)
of a function which takes values in a normed space over `ℝ` or `ℂ`.

At the time of writing, all lemmas in this file
are motivated by the proof of the von Neumann Mean Ergodic Theorem,
see `LinearIsometry.tendsto_birkhoffAverage_orthogonalProjection`.
-/

public section

open Function Set Filter
open scoped Topology ENNReal Uniformity

section

variable {α E : Type*}

/-- The Birkhoff averages of a function `g` over the orbit of a fixed point `x` of `f`
tend to `g x` as `N → ∞`. In fact, they are equal to `g x` for all `N ≠ 0`,
see `Function.IsFixedPt.birkhoffAverage_eq`.

TODO: add a version for a periodic orbit. -/
/-
**Function.IsFixedPt.tendsto_birkhoffAverage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.IsFixedPt.tendsto_birkhoffAverage (R : Type*) [DivisionSemiring R
] [CharZero R] [AddCommMonoid E] [TopologicalSpace E] [Module R E] {f : α -> α} 
{x : α} (h : f.IsFixedPt x) (g : α -> E) : Tendsto (birkhoffAverage R f g · x) a
tTop (𝓝 (g x))
参数：R : Type*；h : f.IsFixedPt x；g : α -> E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.eventually_ne_atTop`：eventually_ne_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, x != a
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.IsFixedPt.birkhoffAverage_eq`：Function.IsFixedPt.birkhoffAverag
e_eq {f : α -> α} {x : α} (h : IsFixedPt f x) (g : α -> M) {n : Nat} (hn : (n : 
R) != 0) : birkhoffAverage …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)

--- 原说明 ---
The Birkhoff averages of a function `g` over the orbit of a fixed point `x` of `
f`
tend to `g x` as `N → ∞`. In fact, they are equal to `g x` for all `N ≠ 0`,
see `Function.IsFixedPt.birkhoffAverage_eq`.

TODO: add a version for a periodic orbit.
-/
theorem Function.IsFixedPt.tendsto_birkhoffAverage
    (R : Type*) [DivisionSemiring R] [CharZero R]
    [AddCommMonoid E] [TopologicalSpace E] [Module R E]
    {f : α → α} {x : α} (h : f.IsFixedPt x) (g : α → E) :
    Tendsto (birkhoffAverage R f g · x) atTop (𝓝 (g x)) :=
  tendsto_const_nhds.congr' <| (eventually_ne_atTop 0).mono fun _n hn ↦
    (h.birkhoffAverage_eq R g (Nat.cast_ne_zero.mpr hn)).symm

variable [NormedAddCommGroup E]
/-
**dist_birkhoffSum_apply_birkhoffSum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_birkhoffSum_apply_birkhoffSum (f : α -> α) (g : α -> E) (n : Nat) (x 
: α) : dist (birkhoffSum f g n (f x)) (birkhoffSum f g n x) = dist (g (f^[n] x))
 (g x)
参数：f : α -> α；g : α -> E；n : Nat；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `birkhoffSum_apply_sub_birkhoffSum`：birkhoffSum_apply_sub_birkhoffSum (f 
: α -> α) (g : α -> G) (n : Nat) (x : α) : birkhoffSum f g n (f x) - birkhoffSum
 f g n x = g (f^[n] x) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dist_birkhoffSum_apply_birkhoffSum (f : α → α) (g : α → E) (n : ℕ) (x : α) :
    dist (birkhoffSum f g n (f x)) (birkhoffSum f g n x) = dist (g (f^[n] x)) (g x) := by
  simp only [dist_eq_norm, birkhoffSum_apply_sub_birkhoffSum]
/-
**dist_birkhoffSum_birkhoffSum_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_birkhoffSum_birkhoffSum_le (f : α -> α) (g : α -> E) (n : Nat) (x y :
 α) : dist (birkhoffSum f g n x) (birkhoffSum f g n y) <= ∑ k in Finset.range n,
 dist (g (f^[k] x)) (g (f^[k] y))
参数：f : α -> α；g : α -> E；n : Nat；x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dist_sum_sum_le`：∀ {ι : Type u_3} {E : Type u_5} [inst : SeminormedAddCo
mmGroup E] (s : Finset ι) (f a : ι → E),   dist (∑ b ∈ s, f b) (∑ b ∈ s, a b) ≤ 
∑ b ∈…
-/
theorem dist_birkhoffSum_birkhoffSum_le (f : α → α) (g : α → E) (n : ℕ) (x y : α) :
    dist (birkhoffSum f g n x) (birkhoffSum f g n y) ≤
      ∑ k ∈ Finset.range n, dist (g (f^[k] x)) (g (f^[k] y)) :=
  dist_sum_sum_le _ _ _

variable (𝕜 : Type*) [RCLike 𝕜] [NormedSpace 𝕜 E]
/-
**dist_birkhoffAverage_birkhoffAverage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_birkhoffAverage_birkhoffAverage (f : α -> α) (g : α -> E) (n : Nat) (
x y : α) : dist (birkhoffAverage 𝕜 f g n x) (birkhoffAverage 𝕜 f g n y) = dist (
birkhoffSum f g n x) (birkhoffSum f g n y) / n
参数：f : α -> α；g : α -> E；n : Nat；x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_smul₀`：dist_smul₀ (s : α) (x y : β) : dist (s • x) (s • y) = ‖s‖ * 
dist x y
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
· 使用定理 `RCLike.norm_natCast`：norm_natCast (n : Nat) : ‖(n : K)‖ = n
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dist_birkhoffAverage_birkhoffAverage (f : α → α) (g : α → E) (n : ℕ) (x y : α) :
    dist (birkhoffAverage 𝕜 f g n x) (birkhoffAverage 𝕜 f g n y) =
      dist (birkhoffSum f g n x) (birkhoffSum f g n y) / n := by
  simp [birkhoffAverage, dist_smul₀, div_eq_inv_mul]
/-
**dist_birkhoffAverage_birkhoffAverage_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_birkhoffAverage_birkhoffAverage_le (f : α -> α) (g : α -> E) (n : Nat
) (x y : α) : dist (birkhoffAverage 𝕜 f g n x) (birkhoffAverage 𝕜 f g n y) <= (∑
 k in Finset.range n, dist (g (f^[k] x)) (g (f^[k] y))) / n
参数：f : α -> α；g : α -> E；n : Nat；x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `dist_birkhoffAverage_birkhoffAverage`：dist_birkhoffAverage_birkhoffAvera
ge (f : α -> α) (g : α -> E) (n : Nat) (x y : α) : dist (birkhoffAverage 𝕜 f g n
 x) (birkhoffAverage 𝕜 f g…
· 使用引理 `div_le_div_of_nonneg_right`：div_le_div_of_nonneg_right (hab : a <= b) (h
c : 0 <= c) : a / c <= b / c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `dist_birkhoffSum_birkhoffSum_le`：dist_birkhoffSum_birkhoffSum_le (f : α 
-> α) (g : α -> E) (n : Nat) (x y : α) : dist (birkhoffSum f g n x) (birkhoffSum
 f g n y) <= ∑ k in F…
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem dist_birkhoffAverage_birkhoffAverage_le (f : α → α) (g : α → E) (n : ℕ) (x y : α) :
    dist (birkhoffAverage 𝕜 f g n x) (birkhoffAverage 𝕜 f g n y) ≤
      (∑ k ∈ Finset.range n, dist (g (f^[k] x)) (g (f^[k] y))) / n :=
  (dist_birkhoffAverage_birkhoffAverage _ _ _ _ _ _).trans_le <| by
    gcongr; apply dist_birkhoffSum_birkhoffSum_le
/-
**dist_birkhoffAverage_apply_birkhoffAverage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_birkhoffAverage_apply_birkhoffAverage (f : α -> α) (g : α -> E) (n : 
Nat) (x : α) : dist (birkhoffAverage 𝕜 f g n (f x)) (birkhoffAverage 𝕜 f g n x) 
= dist (g (f^[n] x)) (g x) / n
参数：f : α -> α；g : α -> E；n : Nat；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_birkhoffAverage_birkhoffAverage`：dist_birkhoffAverage_birkhoffAvera
ge (f : α -> α) (g : α -> E) (n : Nat) (x y : α) : dist (birkhoffAverage 𝕜 f g n
 x) (birkhoffAverage 𝕜 f g…
· 使用定理 `dist_birkhoffSum_apply_birkhoffSum`：dist_birkhoffSum_apply_birkhoffSum (
f : α -> α) (g : α -> E) (n : Nat) (x : α) : dist (birkhoffSum f g n (f x)) (bir
khoffSum f g n x) = dist…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dist_birkhoffAverage_apply_birkhoffAverage (f : α → α) (g : α → E) (n : ℕ) (x : α) :
    dist (birkhoffAverage 𝕜 f g n (f x)) (birkhoffAverage 𝕜 f g n x) =
      dist (g (f^[n] x)) (g x) / n := by
  simp [dist_birkhoffAverage_birkhoffAverage, dist_birkhoffSum_apply_birkhoffSum]

/-- If a function `g` is bounded along the positive orbit of `x` under `f`,
then the difference between Birkhoff averages of `g`
along the orbit of `f x` and along the orbit of `x`
tends to zero.

See also `tendsto_birkhoffAverage_apply_sub_birkhoffAverage'`. -/
/-
**tendsto_birkhoffAverage_apply_sub_birkhoffAverage** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：tendsto_birkhoffAverage_apply_sub_birkhoffAverage {f : α -> α} {g : α -> E
} {x : α} (h : Bornology.IsBounded (range (g <| f^[·] x))) : Tendsto (fun n => b
irkhoffAverage 𝕜 f g n (f x) - birkhoffAverage 𝕜 f g n x) atTop (𝓝 0)
参数：h : Bornology.IsBounded (range (g <| f^[·] x))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.isBounded_range_iff`：isBounded_range_iff {f : β -> α} : IsBounded
 (range f) ↔ exists C, forall x y, dist (f x) (f y) <= C
· 使用定理 `Filter.Tendsto.div_atTop`：Filter.Tendsto.div_atTop {a : 𝕜} (h : Tendsto 
f l (𝓝 a)) (hg : Tendsto g l atTop) : Tendsto (fun x => f x / g x) l (𝓝 0)
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `tendsto_natCast_atTop_atTop`：tendsto_natCast_atTop_atTop [Semiring R] [P
artialOrder R] [IsOrderedRing R] [Archimedean R] : Tendsto ((↑) : Nat -> R) atTo
p atTop
· 使用定理 `squeeze_zero_norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedAdd
Group E] {f : α → E} {a : α → ℝ} {t₀ : Filter α},   (∀ (n : α), ‖f n‖ ≤ a n) → F
ilter.T…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `dist_birkhoffAverage_apply_birkhoffAverage`：dist_birkhoffAverage_apply_b
irkhoffAverage (f : α -> α) (g : α -> E) (n : Nat) (x : α) : dist (birkhoffAvera
ge 𝕜 f g n (f x)) (birkhoffAvera…
· 使用引理 `div_le_div_of_nonneg_right`：div_le_div_of_nonneg_right (hab : a <= b) (h
c : 0 <= c) : a / c <= b / c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α

--- 原说明 ---
If a function `g` is bounded along the positive orbit of `x` under `f`,
then the difference between Birkhoff averages of `g`
along the orbit of `f x` and along the orbit of `x`
tends to zero.

See also `tendsto_birkhoffAverage_apply_sub_birkhoffAverage'`.
-/
theorem tendsto_birkhoffAverage_apply_sub_birkhoffAverage {f : α → α} {g : α → E} {x : α}
    (h : Bornology.IsBounded (range (g <| f^[·] x))) :
    Tendsto (fun n ↦ birkhoffAverage 𝕜 f g n (f x) - birkhoffAverage 𝕜 f g n x) atTop (𝓝 0) := by
  rcases Metric.isBounded_range_iff.1 h with ⟨C, hC⟩
  have : Tendsto (fun n : ℕ ↦ C / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  refine squeeze_zero_norm (fun n ↦ ?_) this
  rw [← dist_eq_norm, dist_birkhoffAverage_apply_birkhoffAverage]
  gcongr
  exact hC n 0

/-- If a function `g` is bounded,
then the difference between Birkhoff averages of `g`
along the orbit of `f x` and along the orbit of `x`
tends to zero.

See also `tendsto_birkhoffAverage_apply_sub_birkhoffAverage`. -/
/-
**tendsto_birkhoffAverage_apply_sub_birkhoffAverage'** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：tendsto_birkhoffAverage_apply_sub_birkhoffAverage' {g : α -> E} (h : Borno
logy.IsBounded (range g)) (f : α -> α) (x : α) : Tendsto (fun n => birkhoffAvera
ge 𝕜 f g n (f x) - birkhoffAverage 𝕜 f g n x) atTop (𝓝 0)
参数：h : Bornology.IsBounded (range g)；f : α -> α；x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_birkhoffAverage_apply_sub_birkhoffAverage`：tendsto_birkhoffAvera
ge_apply_sub_birkhoffAverage {f : α -> α} {g : α -> E} {x : α} (h : Bornology.Is
Bounded (range (g <| f^[·] x))) : Tends…
· 使用定理 `Bornology.IsBounded.subset`：∀ {α : Type u_2} {x : Bornology α} {s t : Se
t α}, Bornology.IsBounded t → s ⊆ t → Bornology.IsBounded s
· 使用定理 `Set.range_comp_subset_range`：range_comp_subset_range (f : α -> β) (g : β
 -> γ) : range (g ∘ f) subseteq range g

--- 原说明 ---
If a function `g` is bounded,
then the difference between Birkhoff averages of `g`
along the orbit of `f x` and along the orbit of `x`
tends to zero.

See also `tendsto_birkhoffAverage_apply_sub_birkhoffAverage`.
-/
theorem tendsto_birkhoffAverage_apply_sub_birkhoffAverage' {g : α → E}
    (h : Bornology.IsBounded (range g)) (f : α → α) (x : α) :
    Tendsto (fun n ↦ birkhoffAverage 𝕜 f g n (f x) - birkhoffAverage 𝕜 f g n x) atTop (𝓝 0) :=
  tendsto_birkhoffAverage_apply_sub_birkhoffAverage _ <| h.subset <| range_comp_subset_range _ _

end

variable (𝕜 : Type*) {X E : Type*}
  [PseudoEMetricSpace X] [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f : X → X} {g : X → E} {l : X → E}

/-- If `f` is a non-strictly contracting map (i.e., it is Lipschitz with constant `1`)
and `g` is a uniformly continuous, then the Birkhoff averages of `g` along orbits of `f`
is a uniformly equicontinuous family of functions. -/
/-
**uniformEquicontinuous_birkhoffAverage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformEquicontinuous_birkhoffAverage (hf : LipschitzWith 1 f) (hg : Unifo
rmContinuous g) : UniformEquicontinuous (birkhoffAverage 𝕜 f g)
参数：hf : LipschitzWith 1 f；hg : UniformContinuous g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.HasBasis.uniformEquicontinuous_iff_right`：Filter.HasBasis.uniform
Equicontinuous_iff_right {p : κ -> Prop} {s : κ -> Set (α × α)} {F : ι -> β -> α
} (hα : (𝓤 α).HasBasis p s) : Uniform…
· 使用定理 `Metric.uniformity_basis_dist_le`：uniformity_basis_dist_le : (𝓤 α).HasBas
is ((0 : Real) < ·) fun ε => { p : α × α | dist p.1 p.2 <= ε }
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.uniformContinuous_iff`：Filter.HasBasis.uniformContinuous
_iff {ι'} {p : ι -> Prop} {s : ι -> SetRel α α} (ha : (𝓤 α).HasBasis p s) {q : ι
' -> Prop} {t : ι' -> Set (…
· 使用定理 `uniformity_basis_edist_le`：uniformity_basis_edist_le : (𝓤 α).HasBasis (f
un ε : Real>=0∞ => 0 < ε) fun ε => { p : α × α | edist p.1 p.2 <= ε }
· 使用定理 `mem_uniformity_edist`：mem_uniformity_edist {s : Set (α × α)} : s in 𝓤 α 
↔ exists ε > 0, forall {a b : α}, edist a b < ε -> (a, b) in s
· 使用定理 `dist_birkhoffAverage_birkhoffAverage_le`：dist_birkhoffAverage_birkhoffAv
erage_le (f : α -> α) (g : α -> E) (n : Nat) (x y : α) : dist (birkhoffAverage 𝕜
 f g n x) (birkhoffAverage 𝕜 …
· 使用引理 `div_le_div_of_nonneg_right`：div_le_div_of_nonneg_right (hab : a <= b) (h
c : 0 <= c) : a / c <= b / c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `LipschitzWith.edist_le_mul_of_le`：edist_le_mul_of_le (h : LipschitzWith 
K f) (hr : edist x y <= r) : edist (f x) (f y) <= K * r
· 使用定理 `LipschitzWith.iterate`：∀ {α : Type u} [inst : PseudoEMetricSpace α] {K :
 NNReal} {f : α → α},   LipschitzWith K f → ∀ (n : ℕ), LipschitzWith (K ^ n) f^[
n]
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
（共 39 条，此处仅展示前 30 条）

--- 原说明 ---
If `f` is a non-strictly contracting map (i.e., it is Lipschitz with constant `1
`)
and `g` is a uniformly continuous, then the Birkhoff averages of `g` along orbit
s of `f`
is a uniformly equicontinuous family of functions.
-/
theorem uniformEquicontinuous_birkhoffAverage (hf : LipschitzWith 1 f) (hg : UniformContinuous g) :
    UniformEquicontinuous (birkhoffAverage 𝕜 f g) := by
  refine Metric.uniformity_basis_dist_le.uniformEquicontinuous_iff_right.2 fun ε hε ↦ ?_
  rcases (uniformity_basis_edist_le.uniformContinuous_iff Metric.uniformity_basis_dist_le).1 hg ε hε
    with ⟨δ, hδ₀, hδε⟩
  refine mem_uniformity_edist.2 ⟨δ, hδ₀, fun {x y} h n ↦ ?_⟩
  calc
    dist (birkhoffAverage 𝕜 f g n x) (birkhoffAverage 𝕜 f g n y)
      ≤ (∑ k ∈ Finset.range n, dist (g (f^[k] x)) (g (f^[k] y))) / n :=
      dist_birkhoffAverage_birkhoffAverage_le ..
    _ ≤ (∑ _k ∈ Finset.range n, ε) / n := by
      gcongr
      refine hδε _ _ ?_
      simpa using (hf.iterate _).edist_le_mul_of_le h.le
    _ = n * ε / n := by simp
    _ ≤ ε := by
      rcases eq_or_ne n 0 with hn | hn <;> simp [hn, hε.le, mul_div_cancel_left₀]

/-- If `f : X → X` is a non-strictly contracting map (i.e., it is Lipschitz with constant `1`),
`g : X → E` is a uniformly continuous, and `l : X → E` is a continuous function,
then the set of points `x`
such that the Birkhoff average of `g` along the orbit of `x` tends to `l x`
is a closed set. -/
/-
**isClosed_setOfPred_tendsto_birkhoffAverage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_setOfPred_tendsto_birkhoffAverage (hf : LipschitzWith 1 f) (hg : 
UniformContinuous g) (hl : Continuous l) : IsClosed {x | Tendsto (birkhoffAverag
e 𝕜 f g · x) atTop (𝓝 (l x))}
参数：hf : LipschitzWith 1 f；hg : UniformContinuous g；hl : Continuous l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equicontinuous.isClosed_setOfPred_tendsto`：Equicontinuous.isClosed_setOf
Pred_tendsto {l : Filter ι} {F : ι -> X -> α} {f : X -> α} (hF : Equicontinuous 
F) (hf : Continuous f) : IsClos…
· 使用定理 `UniformEquicontinuous.equicontinuous`：UniformEquicontinuous.equicontinuo
us {F : ι -> β -> α} (h : UniformEquicontinuous F) : Equicontinuous F
· 使用定理 `uniformEquicontinuous_birkhoffAverage`：uniformEquicontinuous_birkhoffAve
rage (hf : LipschitzWith 1 f) (hg : UniformContinuous g) : UniformEquicontinuous
 (birkhoffAverage 𝕜 f g)

--- 原说明 ---
If `f : X → X` is a non-strictly contracting map (i.e., it is Lipschitz with con
stant `1`),
`g : X → E` is a uniformly continuous, and `l : X → E` is a continuous function,
then the set of points `x`
such that the Birkhoff average of `g` along the orbit of `x` tends to `l x`
is a closed set.
-/
theorem isClosed_setOfPred_tendsto_birkhoffAverage
    (hf : LipschitzWith 1 f) (hg : UniformContinuous g) (hl : Continuous l) :
    IsClosed {x | Tendsto (birkhoffAverage 𝕜 f g · x) atTop (𝓝 (l x))} :=
  (uniformEquicontinuous_birkhoffAverage 𝕜 hf hg).equicontinuous.isClosed_setOfPred_tendsto hl

@[deprecated (since := "2026-07-09")]
alias isClosed_setOf_tendsto_birkhoffAverage := isClosed_setOfPred_tendsto_birkhoffAverage
