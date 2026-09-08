/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Sébastien Gouëzel,
  Rémy Degenne, David Loeffler
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Continuity of power functions

This file contains lemmas about continuity of the power functions on `ℂ`, `ℝ`, `ℝ≥0`, and `ℝ≥0∞`.
-/

public section


noncomputable section

open Real Topology NNReal ENNReal Filter ComplexConjugate Finset Set

section CpowLimits

/-!
## Continuity for complex powers
-/


open Complex

variable {α : Type*}

/-
**zero_cpow_eq_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：zero_cpow_eq_nhds {b : Complex} (hb : b != 0) : (fun x : Complex => (0 : C
omplex) ^ x) =ᶠ[𝓝 b] 0
参数：hb : b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.eventually_mem`：IsOpen.eventually_mem (hs : IsOpen s) (hx : x in 
s) : forallᶠ x in 𝓝 x, x in s
· 使用定理 `isOpen_ne`：isOpen_ne [T1Space X] {x : X} : IsOpen { y | y != x }
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.zero_cpow`：zero_cpow {x : Complex} (h : x != 0) : (0 : Complex) 
^ x = 0
· 使用定理 `Pi.zero_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Zer
o (M i)] (i : ι), 0 i = 0
-/
theorem zero_cpow_eq_nhds {b : ℂ} (hb : b ≠ 0) : (fun x : ℂ => (0 : ℂ) ^ x) =ᶠ[𝓝 b] 0 := by
  suffices ∀ᶠ x : ℂ in 𝓝 b, x ≠ 0 from
    this.mono fun x hx ↦ by
      dsimp only
      rw [zero_cpow hx, Pi.zero_apply]
  exact IsOpen.eventually_mem isOpen_ne hb
/-
**cpow_eq_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cpow_eq_nhds {a b : Complex} (ha : a != 0) : (fun x => x ^ b) =ᶠ[𝓝 a] fun 
x => exp (log x * b)
参数：ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.eventually_mem`：IsOpen.eventually_mem (hs : IsOpen s) (hx : x in 
s) : forallᶠ x in 𝓝 x, x in s
· 使用定理 `isOpen_ne`：isOpen_ne [T1Space X] {x : X} : IsOpen { y | y != x }
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.cpow_def_of_ne_zero`：cpow_def_of_ne_zero {x : Complex} (hx : x !
= 0) (y : Complex) : x ^ y = exp (log x * y)
-/
theorem cpow_eq_nhds {a b : ℂ} (ha : a ≠ 0) :
    (fun x => x ^ b) =ᶠ[𝓝 a] fun x => exp (log x * b) := by
  suffices ∀ᶠ x : ℂ in 𝓝 a, x ≠ 0 from
    this.mono fun x hx ↦ by
      dsimp only
      rw [cpow_def_of_ne_zero hx]
  exact IsOpen.eventually_mem isOpen_ne ha
/-
**cpow_eq_nhds'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cpow_eq_nhds' {p : Complex × Complex} (hp_fst : p.fst != 0) : (fun x => x.
1 ^ x.2) =ᶠ[𝓝 p] fun x => exp (log x.1 * x.2)
参数：hp_fst : p.fst != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isOpen_compl_iff`：∀ {X : Type u} {s : Set X} [inst : TopologicalSpace X]
, IsOpen sᶜ ↔ IsClosed s
· 使用定理 `isClosed_eq`：isClosed_eq [T2Space X] {f g : Y -> X} (hf : Continuous f) 
(hg : Continuous g) : IsClosed { y : Y | f y = g y }
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists t subseteq s, IsOpen t ∧ 
x in t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.cpow_def_of_ne_zero`：cpow_def_of_ne_zero {x : Complex} (hx : x !
= 0) (y : Complex) : x ^ y = exp (log x * y)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cpow_eq_nhds' {p : ℂ × ℂ} (hp_fst : p.fst ≠ 0) :
    (fun x => x.1 ^ x.2) =ᶠ[𝓝 p] fun x => exp (log x.1 * x.2) := by
  suffices IsOpen {x : ℂ × ℂ | x.1 = 0}ᶜ from
    mem_nhds_iff.mpr ⟨_, fun x hx ↦ by simp_all [cpow_def_of_ne_zero], this, hp_fst⟩
  rw [isOpen_compl_iff]
  exact isClosed_eq continuous_fst continuous_const

-- Continuity of `fun x => a ^ x`: union of these two lemmas is optimal.
/-
**continuousAt_const_cpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousAt_const_cpow {a b : Complex} (ha : a != 0) : ContinuousAt (fun 
x : Complex => a ^ x) b
参数：ha : a != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.cpow_def_of_ne_zero`：cpow_def_of_ne_zero {x : Complex} (hx : x !
= 0) (y : Complex) : x ^ y = exp (log x * y)
· 使用定理 `ContinuousAt.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace
 Z] {f …
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `Complex.continuous_exp`：continuous_exp : Continuous exp
· 使用定理 `ContinuousAt.mul`：ContinuousAt.mul (hf : ContinuousAt f x) (hg : Continu
ousAt g x) : ContinuousAt (f * g) x
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
· 使用定理 `continuousAt_const`：continuousAt_const : ContinuousAt (fun _ : X => y) x
· 使用定理 `continuousAt_id`：continuousAt_id : ContinuousAt id x
-/
theorem continuousAt_const_cpow {a b : ℂ} (ha : a ≠ 0) : ContinuousAt (fun x : ℂ => a ^ x) b := by
  have cpow_eq : (fun x : ℂ => a ^ x) = fun x => exp (log a * x) := by
    ext1 b
    rw [cpow_def_of_ne_zero ha]
  rw [cpow_eq]
  exact continuous_exp.continuousAt.comp (ContinuousAt.mul continuousAt_const continuousAt_id)
/-
**continuousAt_const_cpow'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousAt_const_cpow' {a b : Complex} (h : b != 0) : ContinuousAt (fun 
x : Complex => a ^ x) b
参数：h : b != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuousAt_congr`：continuousAt_congr {g : X -> Y} (h : f =ᶠ[𝓝 x] g) : 
ContinuousAt f x ↔ ContinuousAt g x
· 使用定理 `zero_cpow_eq_nhds`：zero_cpow_eq_nhds {b : Complex} (hb : b != 0) : (fun 
x : Complex => (0 : Complex) ^ x) =ᶠ[𝓝 b] 0
· 使用定理 `continuousAt_const`：continuousAt_const : ContinuousAt (fun _ : X => y) x
· 使用定理 `continuousAt_const_cpow`：continuousAt_const_cpow {a b : Complex} (ha : a
 != 0) : ContinuousAt (fun x : Complex => a ^ x) b
-/
theorem continuousAt_const_cpow' {a b : ℂ} (h : b ≠ 0) : ContinuousAt (fun x : ℂ => a ^ x) b := by
  by_cases ha : a = 0
  · rw [ha, continuousAt_congr (zero_cpow_eq_nhds h)]
    exact continuousAt_const
  · exact continuousAt_const_cpow ha

/-- The function `z ^ w` is continuous in `(z, w)` provided that `z` does not belong to the interval
`(-∞, 0]` on the real line. See also `Complex.continuousAt_cpow_zero_of_re_pos` for a version that
works for `z = 0` but assumes `0 < re w`. -/
/-
**continuousAt_cpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousAt_cpow {p : Complex × Complex} (hp_fst : p.fst in slitPlane) : 
ContinuousAt (fun x : Complex × Complex => x.1 ^ x.2) p
参数：hp_fst : p.fst in slitPlane。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuousAt_congr`：continuousAt_congr {g : X -> Y} (h : f =ᶠ[𝓝 x] g) : 
ContinuousAt f x ↔ ContinuousAt g x
· 使用定理 `cpow_eq_nhds'`：cpow_eq_nhds' {p : Complex × Complex} (hp_fst : p.fst != 
0) : (fun x => x.1 ^ x.2) =ᶠ[𝓝 p] fun x => exp (log x.1 * x.2)
· 使用定理 `Complex.slitPlane_ne_zero`：∀ {z : ℂ}, z ∈ Complex.slitPlane → z ≠ 0
· 使用定理 `ContinuousAt.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace
 Z] {f …
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `Complex.continuous_exp`：continuous_exp : Continuous exp
· 使用定理 `ContinuousAt.mul`：ContinuousAt.mul (hf : ContinuousAt f x) (hg : Continu
ousAt g x) : ContinuousAt (f * g) x
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
· 使用定理 `continuousAt_clog`：continuousAt_clog {x : Complex} (h : x in slitPlane) 
: ContinuousAt log x
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)

--- 原说明 ---
The function `z ^ w` is continuous in `(z, w)` provided that `z` does not belong
 to the interval
`(-∞, 0]` on the real line. See also `Complex.continuousAt_cpow_zero_of_re_pos` 
for a version that
works for `z = 0` but assumes `0 < re w`.
-/
theorem continuousAt_cpow {p : ℂ × ℂ} (hp_fst : p.fst ∈ slitPlane) :
    ContinuousAt (fun x : ℂ × ℂ => x.1 ^ x.2) p := by
  rw [continuousAt_congr (cpow_eq_nhds' <| slitPlane_ne_zero hp_fst)]
  refine continuous_exp.continuousAt.comp ?_
  exact
    ContinuousAt.mul
      (ContinuousAt.comp (continuousAt_clog hp_fst) continuous_fst.continuousAt)
      continuous_snd.continuousAt
/-
**continuousAt_cpow_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousAt_cpow_const {a b : Complex} (ha : a in slitPlane) : Continuous
At (· ^ b) a
参数：ha : a in slitPlane。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `continuousAt_cpow`：continuousAt_cpow {p : Complex × Complex} (hp_fst : p
.fst in slitPlane) : ContinuousAt (fun x : Complex × Complex => x.1 ^ x.2) p
· 使用定理 `ContinuousAt.prodMk`：ContinuousAt.prodMk {f : X -> Y} {g : X -> Z} {x : 
X} (hf : ContinuousAt f x) (hg : ContinuousAt g x) : ContinuousAt (fun x => (f x
, g x)) x
· 使用定理 `continuousAt_id`：continuousAt_id : ContinuousAt id x
· 使用定理 `continuousAt_const`：continuousAt_const : ContinuousAt (fun _ : X => y) x
-/
theorem continuousAt_cpow_const {a b : ℂ} (ha : a ∈ slitPlane) :
    ContinuousAt (· ^ b) a :=
  Tendsto.comp (@continuousAt_cpow (a, b) ha) (continuousAt_id.prodMk continuousAt_const)
/-
**Filter.Tendsto.cpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.cpow {l : Filter α} {f g : α -> Complex} {a b : Complex} (h
f : Tendsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b)) (ha : a in slitPlane) : Tendsto 
(fun x => f x ^ g x) l (𝓝 (a ^ b))
参数：hf : Tendsto f l (𝓝 a)；hg : Tendsto g l (𝓝 b)；ha : a in slitPlane。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
· 使用定理 `continuousAt_cpow`：continuousAt_cpow {p : Complex × Complex} (hp_fst : p
.fst in slitPlane) : ContinuousAt (fun x : Complex × Complex => x.1 ^ x.2) p
· 使用定理 `Filter.Tendsto.prodMk_nhds`：Filter.Tendsto.prodMk_nhds {γ} {x : X} {y : 
Y} {f : Filter γ} {mx : γ -> X} {my : γ -> Y} (hx : Tendsto mx f (𝓝 x)) (hy : Te
ndsto my f (𝓝 y)…
-/
theorem Filter.Tendsto.cpow {l : Filter α} {f g : α → ℂ} {a b : ℂ} (hf : Tendsto f l (𝓝 a))
    (hg : Tendsto g l (𝓝 b)) (ha : a ∈ slitPlane) :
    Tendsto (fun x => f x ^ g x) l (𝓝 (a ^ b)) :=
  (@continuousAt_cpow (a, b) ha).tendsto.comp (hf.prodMk_nhds hg)
/-
**Filter.Tendsto.const_cpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.const_cpow {l : Filter α} {f : α -> Complex} {a b : Complex
} (hf : Tendsto f l (𝓝 b)) (h : a != 0 ∨ b != 0) : Tendsto (fun x => a ^ f x) l 
(𝓝 (a ^ b))
参数：hf : Tendsto f l (𝓝 b)；h : a != 0 ∨ b != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
· 使用定理 `continuousAt_const_cpow`：continuousAt_const_cpow {a b : Complex} (ha : a
 != 0) : ContinuousAt (fun x : Complex => a ^ x) b
· 使用定理 `continuousAt_const_cpow'`：continuousAt_const_cpow' {a b : Complex} (h : 
b != 0) : ContinuousAt (fun x : Complex => a ^ x) b
-/
theorem Filter.Tendsto.const_cpow {l : Filter α} {f : α → ℂ} {a b : ℂ} (hf : Tendsto f l (𝓝 b))
    (h : a ≠ 0 ∨ b ≠ 0) : Tendsto (fun x => a ^ f x) l (𝓝 (a ^ b)) := by
  cases h with
  | inl h => exact (continuousAt_const_cpow h).tendsto.comp hf
  | inr h => exact (continuousAt_const_cpow' h).tendsto.comp hf

variable [TopologicalSpace α] {f g : α → ℂ} {s : Set α} {a : α}

nonrec theorem ContinuousWithinAt.cpow (hf : ContinuousWithinAt f s a)
    (hg : ContinuousWithinAt g s a) (h0 : f a ∈ slitPlane) :
    ContinuousWithinAt (fun x => f x ^ g x) s a :=
  hf.cpow hg h0

nonrec theorem ContinuousWithinAt.const_cpow {b : ℂ} (hf : ContinuousWithinAt f s a)
    (h : b ≠ 0 ∨ f a ≠ 0) : ContinuousWithinAt (fun x => b ^ f x) s a :=
  hf.const_cpow h

nonrec theorem ContinuousAt.cpow (hf : ContinuousAt f a) (hg : ContinuousAt g a)
    (h0 : f a ∈ slitPlane) : ContinuousAt (fun x => f x ^ g x) a :=
  hf.cpow hg h0

nonrec theorem ContinuousAt.const_cpow {b : ℂ} (hf : ContinuousAt f a) (h : b ≠ 0 ∨ f a ≠ 0) :
    ContinuousAt (fun x => b ^ f x) a :=
  hf.const_cpow h
/-
**ContinuousOn.cpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.cpow (hf : ContinuousOn f s) (hg : ContinuousOn g s) (h0 : fo
rall a in s, f a in slitPlane) : ContinuousOn (fun x => f x ^ g x) s
参数：hf : ContinuousOn f s；hg : ContinuousOn g s；h0 : forall a in s, f a in slitPl
ane。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.cpow`：∀ {α : Type u_1} [inst : TopologicalSpace α] {f
 g : α → ℂ} {s : Set α} {a : α},   ContinuousWithinAt f s a →     ContinuousWith
inAt g s a → …
-/
theorem ContinuousOn.cpow (hf : ContinuousOn f s) (hg : ContinuousOn g s)
    (h0 : ∀ a ∈ s, f a ∈ slitPlane) : ContinuousOn (fun x => f x ^ g x) s := fun a ha =>
  (hf a ha).cpow (hg a ha) (h0 a ha)
/-
**ContinuousOn.const_cpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.const_cpow {b : Complex} (hf : ContinuousOn f s) (h : b != 0 
∨ forall a in s, f a != 0) : ContinuousOn (fun x => b ^ f x) s
参数：hf : ContinuousOn f s；h : b != 0 ∨ forall a in s, f a != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.const_cpow`：∀ {α : Type u_1} [inst : TopologicalSpace
 α] {f : α → ℂ} {s : Set α} {a : α} {b : ℂ},   ContinuousWithinAt f s a → b ≠ 0 
∨ f a ≠ 0 → Continu…
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
-/
theorem ContinuousOn.const_cpow {b : ℂ} (hf : ContinuousOn f s) (h : b ≠ 0 ∨ ∀ a ∈ s, f a ≠ 0) :
    ContinuousOn (fun x => b ^ f x) s := fun a ha => (hf a ha).const_cpow (h.imp id fun h => h a ha)
/-
**Continuous.cpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.cpow (hf : Continuous f) (hg : Continuous g) (h0 : forall a, f 
a in slitPlane) : Continuous fun x => f x ^ g x
参数：hf : Continuous f；hg : Continuous g；h0 : forall a, f a in slitPlane。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `ContinuousAt.cpow`：∀ {α : Type u_1} [inst : TopologicalSpace α] {f g : α
 → ℂ} {a : α},   ContinuousAt f a → ContinuousAt g a → f a ∈ Complex.slitPlane →
 Contin…
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
-/
theorem Continuous.cpow (hf : Continuous f) (hg : Continuous g)
    (h0 : ∀ a, f a ∈ slitPlane) : Continuous fun x => f x ^ g x :=
  continuous_iff_continuousAt.2 fun a => hf.continuousAt.cpow hg.continuousAt (h0 a)
/-
**Continuous.const_cpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.const_cpow {b : Complex} (hf : Continuous f) (h : b != 0 ∨ fora
ll a, f a != 0) : Continuous fun x => b ^ f x
参数：hf : Continuous f；h : b != 0 ∨ forall a, f a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `ContinuousAt.const_cpow`：∀ {α : Type u_1} [inst : TopologicalSpace α] {f
 : α → ℂ} {a : α} {b : ℂ},   ContinuousAt f a → b ≠ 0 ∨ f a ≠ 0 → ContinuousAt (
fun x => b ^ …
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
-/
theorem Continuous.const_cpow {b : ℂ} (hf : Continuous f) (h : b ≠ 0 ∨ ∀ a, f a ≠ 0) :
    Continuous fun x => b ^ f x :=
  continuous_iff_continuousAt.2 fun a => hf.continuousAt.const_cpow <| h.imp id fun h => h a
/-
**ContinuousOn.cpow_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.cpow_const {b : Complex} (hf : ContinuousOn f s) (h : forall 
a : α, a in s -> f a in slitPlane) : ContinuousOn (fun x => f x ^ b) s
参数：hf : ContinuousOn f s；h : forall a : α, a in s -> f a in slitPlane。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.cpow`：ContinuousOn.cpow (hf : ContinuousOn f s) (hg : Conti
nuousOn g s) (h0 : forall a in s, f a in slitPlane) : ContinuousOn (fun x => f x
 ^ g x)…
· 使用定理 `continuousOn_const`：continuousOn_const {s : Set α} {c : β} : ContinuousO
n (fun _ => c) s
-/
theorem ContinuousOn.cpow_const {b : ℂ} (hf : ContinuousOn f s)
    (h : ∀ a : α, a ∈ s → f a ∈ slitPlane) : ContinuousOn (fun x => f x ^ b) s :=
  hf.cpow continuousOn_const h

@[fun_prop]
/-
**continuous_const_cpow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：continuous_const_cpow (z : Complex) [NeZero z] : Continuous fun s : Comple
x => z ^ s
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.const_cpow`：Continuous.const_cpow {b : Complex} (hf : Continu
ous f) (h : b != 0 ∨ forall a, f a != 0) : Continuous fun x => b ^ f x
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
-/
lemma continuous_const_cpow (z : ℂ) [NeZero z] : Continuous fun s : ℂ ↦ z ^ s :=
  continuous_id.const_cpow (.inl <| NeZero.ne z)

end CpowLimits

section RpowLimits

/-!
## Continuity for real powers
-/


namespace Real

/-
**Real.continuousAt_const_rpow** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：continuousAt_const_rpow {a b : Real} (h : a != 0) : ContinuousAt (a ^ ·) b
参数：h : a != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace
 Z] {f …
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `Complex.continuous_re`：Continuous Complex.re
· 使用定理 `continuousAt_const_cpow`：continuousAt_const_cpow {a b : Complex} (ha : a
 != 0) : ContinuousAt (fun x : Complex => a ^ x) b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Complex.continuous_ofReal`：Continuous Complex.ofReal
-/
theorem continuousAt_const_rpow {a b : ℝ} (h : a ≠ 0) : ContinuousAt (a ^ ·) b := by
  simp only [rpow_def]
  refine Complex.continuous_re.continuousAt.comp ?_
  refine (continuousAt_const_cpow ?_).comp Complex.continuous_ofReal.continuousAt
  norm_cast
/-
**Real.continuousAt_const_rpow'** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：continuousAt_const_rpow' {a b : Real} (h : b != 0) : ContinuousAt (a ^ ·) 
b
参数：h : b != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace
 Z] {f …
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `Complex.continuous_re`：Continuous Complex.re
· 使用定理 `continuousAt_const_cpow'`：continuousAt_const_cpow' {a b : Complex} (h : 
b != 0) : ContinuousAt (fun x : Complex => a ^ x) b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Complex.continuous_ofReal`：Continuous Complex.ofReal
-/
theorem continuousAt_const_rpow' {a b : ℝ} (h : b ≠ 0) : ContinuousAt (a ^ ·) b := by
  simp only [rpow_def]
  refine Complex.continuous_re.continuousAt.comp ?_
  refine (continuousAt_const_cpow' ?_).comp Complex.continuous_ofReal.continuousAt
  norm_cast
/-
**Real.rpow_eq_nhds_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_eq_nhds_of_neg {p : Real × Real} (hp_fst : p.fst < 0) : (fun x : Real
 × Real => x.1 ^ x.2) =ᶠ[𝓝 p] fun x => exp (log x.1 * x.2) * cos (x.2 * π)
参数：hp_fst : p.fst < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.eventually_mem`：IsOpen.eventually_mem (hs : IsOpen s) (hx : x in 
s) : forallᶠ x in 𝓝 x, x in s
· 使用定理 `isOpen_lt`：isOpen_lt [TopologicalSpace β] {f g : β -> α} (hf : Continuou
s f) (hg : Continuous g) : IsOpen { b | f b < g b }
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_def_of_neg`：rpow_def_of_neg {x : Real} (hx : x < 0) (y : Real)
 : x ^ y = exp (log x * y) * cos (y * π)
-/
theorem rpow_eq_nhds_of_neg {p : ℝ × ℝ} (hp_fst : p.fst < 0) :
    (fun x : ℝ × ℝ => x.1 ^ x.2) =ᶠ[𝓝 p] fun x => exp (log x.1 * x.2) * cos (x.2 * π) := by
  suffices ∀ᶠ x : ℝ × ℝ in 𝓝 p, x.1 < 0 from
    this.mono fun x hx ↦ by
      dsimp only
      rw [rpow_def_of_neg hx]
  exact IsOpen.eventually_mem (isOpen_lt continuous_fst continuous_const) hp_fst
/-
**Real.rpow_eq_nhds_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_eq_nhds_of_pos {p : Real × Real} (hp_fst : 0 < p.fst) : (fun x : Real
 × Real => x.1 ^ x.2) =ᶠ[𝓝 p] fun x => exp (log x.1 * x.2)
参数：hp_fst : 0 < p.fst。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.eventually_mem`：IsOpen.eventually_mem (hs : IsOpen s) (hx : x in 
s) : forallᶠ x in 𝓝 x, x in s
· 使用定理 `isOpen_lt`：isOpen_lt [TopologicalSpace β] {f g : β -> α} (hf : Continuou
s f) (hg : Continuous g) : IsOpen { b | f b < g b }
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_def_of_pos`：rpow_def_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : x ^ y = exp (log x * y)
-/
theorem rpow_eq_nhds_of_pos {p : ℝ × ℝ} (hp_fst : 0 < p.fst) :
    (fun x : ℝ × ℝ => x.1 ^ x.2) =ᶠ[𝓝 p] fun x => exp (log x.1 * x.2) := by
  suffices ∀ᶠ x : ℝ × ℝ in 𝓝 p, 0 < x.1 from
    this.mono fun x hx ↦ by
      dsimp only
      rw [rpow_def_of_pos hx]
  exact IsOpen.eventually_mem (isOpen_lt continuous_const continuous_fst) hp_fst
/-
**Real.continuousAt_rpow_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：continuousAt_rpow_of_ne (p : Real × Real) (hp : p.1 != 0) : ContinuousAt (
fun p : Real × Real => p.1 ^ p.2) p
参数：p : Real × Real；hp : p.1 != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ne_iff_lt_or_gt`：ne_iff_lt_or_gt : a != b ↔ a < b ∨ b < a
· 使用定理 `continuousAt_congr`：continuousAt_congr {g : X -> Y} (h : f =ᶠ[𝓝 x] g) : 
ContinuousAt f x ↔ ContinuousAt g x
· 使用定理 `Real.rpow_eq_nhds_of_neg`：rpow_eq_nhds_of_neg {p : Real × Real} (hp_fst 
: p.fst < 0) : (fun x : Real × Real => x.1 ^ x.2) =ᶠ[𝓝 p] fun x => exp (log x.1 
* x.2) * cos (…
· 使用定理 `ContinuousAt.mul`：ContinuousAt.mul (hf : ContinuousAt f x) (hg : Continu
ousAt g x) : ContinuousAt (f * g) x
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `ContinuousAt.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace
 Z] {f …
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `Real.continuous_exp`：continuous_exp : Continuous exp
· 使用定理 `Real.continuousAt_log`：continuousAt_log (hx : x != 0) : ContinuousAt log
 x
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)
· 使用定理 `ContinuousAt.comp'`：ContinuousAt.comp' {g : Y -> Z} {x : X} (hg : Contin
uousAt g (f x)) (hf : ContinuousAt f x) : ContinuousAt (fun x => g (f x)) x
· 使用定理 `Real.continuous_cos`：continuous_cos : Continuous cos
· 使用定理 `ContinuousAt.mul_const`：ContinuousAt.mul_const (hf : ContinuousAt f x) (
b : M) : ContinuousAt (f · * b) x
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `ContinuousAt.snd`：ContinuousAt.snd {f : X -> Y × Z} {x : X} (hf : Contin
uousAt f x) : ContinuousAt (fun x : X => (f x).2) x
· 使用定理 `continuousAt_id'`：continuousAt_id' (y) : ContinuousAt (fun x : X => x) y
· 使用定理 `Real.rpow_eq_nhds_of_pos`：rpow_eq_nhds_of_pos {p : Real × Real} (hp_fst 
: 0 < p.fst) : (fun x : Real × Real => x.1 ^ x.2) =ᶠ[𝓝 p] fun x => exp (log x.1 
* x.2)
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
theorem continuousAt_rpow_of_ne (p : ℝ × ℝ) (hp : p.1 ≠ 0) :
    ContinuousAt (fun p : ℝ × ℝ => p.1 ^ p.2) p := by
  rw [ne_iff_lt_or_gt] at hp
  cases hp with
  | inl hp =>
    rw [continuousAt_congr (rpow_eq_nhds_of_neg hp)]
    refine ContinuousAt.mul ?_ (by fun_prop)
    · refine continuous_exp.continuousAt.comp (ContinuousAt.mul ?_ continuous_snd.continuousAt)
      exact (continuousAt_log hp.ne).comp continuous_fst.continuousAt
  | inr hp =>
    rw [continuousAt_congr (rpow_eq_nhds_of_pos hp)]
    refine continuous_exp.continuousAt.comp (ContinuousAt.mul ?_ continuous_snd.continuousAt)
    refine (continuousAt_log ?_).comp continuous_fst.continuousAt
    exact hp.ne'
/-
**Real.continuousAt_rpow_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：continuousAt_rpow_of_pos (p : Real × Real) (hp : 0 < p.2) : ContinuousAt (
fun p : Real × Real => p.1 ^ p.2) p
参数：p : Real × Real；hp : 0 < p.2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_or_eq`：ne_or_eq {α : Sort*} (x y : α) : x != y ∨ x = y
· 使用定理 `Real.continuousAt_rpow_of_ne`：continuousAt_rpow_of_ne (p : Real × Real) 
(hp : p.1 != 0) : ContinuousAt (fun p : Real × Real => p.1 ^ p.2) p
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Real.tendsto_exp_atBot`：tendsto_exp_atBot : Tendsto exp atBot (𝓝 0)
· 使用定理 `Filter.Tendsto.atBot_mul_pos`：Filter.Tendsto.atBot_mul_pos {C : 𝕜} (hC :
 0 < C) (hf : Tendsto f l atBot) (hg : Tendsto g l (𝓝 C)) : Tendsto (fun x => f 
x * g x) l atBot
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Real.tendsto_log_nhdsNE_zero`：tendsto_log_nhdsNE_zero : Tendsto log (𝓝[!
=] 0) atBot
· 使用定理 `Filter.tendsto_fst`：tendsto_fst : Tendsto Prod.fst (f ×ˢ g) f
· 使用定理 `Filter.tendsto_snd`：tendsto_snd : Tendsto Prod.snd (f ×ˢ g) g
· 使用定理 `squeeze_zero_norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedAdd
Group E] {f : α → E} {a : α → ℝ} {t₀ : Filter α},   (∀ (n : α), ‖f n‖ ≤ a n) → F
ilter.T…
· 使用定理 `Real.abs_rpow_le_exp_log_mul`：abs_rpow_le_exp_log_mul (x y : Real) : |x 
^ y| <= exp (log x * y)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsWithin_singleton`：nhdsWithin_singleton (a : α) : 𝓝[{a}] a = pure a
· 使用定理 `Filter.tendsto_pure`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {a : Fi
lter α} {b : β},   Filter.Tendsto f a (pure b) ↔ ∀ᶠ (x : α) in a, f x = b
· 使用定理 `Filter.pure_prod`：pure_prod {a : α} {f : Filter β} : pure a ×ˢ f = map (
Prod.mk a) f
· 使用定理 `Filter.eventually_map`：eventually_map {P : β -> Prop} : (forallᶠ b in ma
p m f, P b) ↔ forallᶠ a in f, P (m a)
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `lt_mem_nhds`：lt_mem_nhds [OrderTopology α] {a b : α} (h : a < b) : foral
lᶠ x in 𝓝 b, a < x
· 使用定理 `Real.zero_rpow`：zero_rpow {x : Real} (h : x != 0) : (0 : Real) ^ x = 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.compl_union_self`：compl_union_self (s : Set α) : sᶜ union s = univ
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
· 使用定理 `Filter.Tendsto.sup`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x₁ x₂ :
 Filter α} {y : Filter β},   Filter.Tendsto f x₁ y → Filter.Tendsto f x₂ y → Fil
ter.Tend…
· 使用定理 `Filter.Tendsto.mono_right`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
x : Filter α} {y z : Filter β},   Filter.Tendsto f x y → y ≤ z → Filter.Tendsto 
f x z
· 使用定理 `pure_le_nhds`：pure_le_nhds : pure <= (𝓝 : X -> Filter X)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem continuousAt_rpow_of_pos (p : ℝ × ℝ) (hp : 0 < p.2) :
    ContinuousAt (fun p : ℝ × ℝ => p.1 ^ p.2) p := by
  obtain ⟨x, y⟩ := p
  dsimp only at hp
  obtain hx | rfl := ne_or_eq x 0
  · exact continuousAt_rpow_of_ne (x, y) hx
  have A : Tendsto (fun p : ℝ × ℝ => exp (log p.1 * p.2)) (𝓝[≠] 0 ×ˢ 𝓝 y) (𝓝 0) :=
    tendsto_exp_atBot.comp
      ((tendsto_log_nhdsNE_zero.comp tendsto_fst).atBot_mul_pos hp tendsto_snd)
  have B : Tendsto (fun p : ℝ × ℝ => p.1 ^ p.2) (𝓝[≠] 0 ×ˢ 𝓝 y) (𝓝 0) :=
    squeeze_zero_norm (fun p => abs_rpow_le_exp_log_mul p.1 p.2) A
  have C : Tendsto (fun p : ℝ × ℝ => p.1 ^ p.2) (𝓝[{0}] 0 ×ˢ 𝓝 y) (pure 0) := by
    rw [nhdsWithin_singleton, tendsto_pure, pure_prod, eventually_map]
    exact (lt_mem_nhds hp).mono fun y hy => zero_rpow hy.ne'
  simpa only [← sup_prod, ← nhdsWithin_union, compl_union_self, nhdsWithin_univ, nhds_prod_eq,
    ContinuousAt, zero_rpow hp.ne'] using B.sup (C.mono_right (pure_le_nhds _))
/-
**Real.continuousAt_rpow** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：continuousAt_rpow (p : Real × Real) (h : p.1 != 0 ∨ 0 < p.2) : ContinuousA
t (fun p : Real × Real => p.1 ^ p.2) p
参数：p : Real × Real；h : p.1 != 0 ∨ 0 < p.2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Real.continuousAt_rpow_of_ne`：continuousAt_rpow_of_ne (p : Real × Real) 
(hp : p.1 != 0) : ContinuousAt (fun p : Real × Real => p.1 ^ p.2) p
· 使用定理 `Real.continuousAt_rpow_of_pos`：continuousAt_rpow_of_pos (p : Real × Real
) (hp : 0 < p.2) : ContinuousAt (fun p : Real × Real => p.1 ^ p.2) p
-/
theorem continuousAt_rpow (p : ℝ × ℝ) (h : p.1 ≠ 0 ∨ 0 < p.2) :
    ContinuousAt (fun p : ℝ × ℝ => p.1 ^ p.2) p :=
  h.elim (fun h => continuousAt_rpow_of_ne p h) fun h => continuousAt_rpow_of_pos p h

@[fun_prop]
/-
**Real.continuousAt_rpow_const** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：continuousAt_rpow_const (x : Real) (q : Real) (h : x != 0 ∨ 0 <= q) : Cont
inuousAt (fun x : Real => x ^ q) x
参数：x : Real；q : Real；h : x != 0 ∨ 0 <= q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `or_assoc`：∀ {a b c : Prop}, (a ∨ b) ∨ c ↔ a ∨ b ∨ c
· 使用引理 `le_iff_lt_or_eq`：le_iff_lt_or_eq : a <= b ↔ a < b ∨ a = b
· 使用定理 `ContinuousAt.comp₂`：ContinuousAt.comp₂ {f : Y × Z -> W} {g : X -> Y} {h 
: X -> Z} {x : X} (hf : ContinuousAt f (g x, h x)) (hg : ContinuousAt g x) (hh :
 Continu…
· 使用定理 `Real.continuousAt_rpow`：continuousAt_rpow (p : Real × Real) (h : p.1 != 
0 ∨ 0 < p.2) : ContinuousAt (fun p : Real × Real => p.1 ^ p.2) p
· 使用定理 `continuousAt_id`：continuousAt_id : ContinuousAt id x
· 使用定理 `continuousAt_const`：continuousAt_const : ContinuousAt (fun _ : X => y) x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.rpow_zero`：rpow_zero (x : Real) : x ^ (0 : Real) = 1
-/
theorem continuousAt_rpow_const (x : ℝ) (q : ℝ) (h : x ≠ 0 ∨ 0 ≤ q) :
    ContinuousAt (fun x : ℝ => x ^ q) x := by
  rw [le_iff_lt_or_eq, ← or_assoc] at h
  obtain h | rfl := h
  · exact (continuousAt_rpow (x, q) h).comp₂ continuousAt_id continuousAt_const
  · simp_rw [rpow_zero]; exact continuousAt_const

@[fun_prop]
/-
**Real.continuous_rpow_const** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：continuous_rpow_const {q : Real} (h : 0 <= q) : Continuous (fun x : Real =
> x ^ q)
参数：h : 0 <= q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `Real.continuousAt_rpow_const`：continuousAt_rpow_const (x : Real) (q : Re
al) (h : x != 0 ∨ 0 <= q) : ContinuousAt (fun x : Real => x ^ q) x
-/
theorem continuous_rpow_const {q : ℝ} (h : 0 ≤ q) : Continuous (fun x : ℝ => x ^ q) :=
  continuous_iff_continuousAt.mpr fun x ↦ continuousAt_rpow_const x q (.inr h)

@[fun_prop]
/-
**Real.continuous_const_rpow** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：continuous_const_rpow {a : Real} (h : a != 0) : Continuous (fun x : Real =
> a ^ x)
参数：h : a != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `Real.continuousAt_const_rpow`：continuousAt_const_rpow {a b : Real} (h : 
a != 0) : ContinuousAt (a ^ ·) b
-/
lemma continuous_const_rpow {a : ℝ} (h : a ≠ 0) : Continuous (fun x : ℝ ↦ a ^ x) :=
  continuous_iff_continuousAt.mpr fun _ ↦ continuousAt_const_rpow h

end Real

section

variable {α : Type*}

/-
**Filter.Tendsto.rpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.rpow {l : Filter α} {f g : α -> Real} {x y : Real} (hf : Te
ndsto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) (h : x != 0 ∨ 0 < y) : Tendsto (fun t 
=> f t ^ g t) l (𝓝 (x ^ y))
参数：hf : Tendsto f l (𝓝 x)；hg : Tendsto g l (𝓝 y)；h : x != 0 ∨ 0 < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
· 使用定理 `Real.continuousAt_rpow`：continuousAt_rpow (p : Real × Real) (h : p.1 != 
0 ∨ 0 < p.2) : ContinuousAt (fun p : Real × Real => p.1 ^ p.2) p
· 使用定理 `Filter.Tendsto.prodMk_nhds`：Filter.Tendsto.prodMk_nhds {γ} {x : X} {y : 
Y} {f : Filter γ} {mx : γ -> X} {my : γ -> Y} (hx : Tendsto mx f (𝓝 x)) (hy : Te
ndsto my f (𝓝 y)…
-/
theorem Filter.Tendsto.rpow {l : Filter α} {f g : α → ℝ} {x y : ℝ} (hf : Tendsto f l (𝓝 x))
    (hg : Tendsto g l (𝓝 y)) (h : x ≠ 0 ∨ 0 < y) : Tendsto (fun t => f t ^ g t) l (𝓝 (x ^ y)) :=
  (Real.continuousAt_rpow (x, y) h).tendsto.comp (hf.prodMk_nhds hg)
/-
**Filter.Tendsto.rpow_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.rpow_const {l : Filter α} {f : α -> Real} {x p : Real} (hf 
: Tendsto f l (𝓝 x)) (h : x != 0 ∨ 0 <= p) : Tendsto (fun a => f a ^ p) l (𝓝 (x 
^ p))
参数：hf : Tendsto f l (𝓝 x)；h : x != 0 ∨ 0 <= p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.rpow_zero`：rpow_zero (x : Real) : x ^ (0 : Real) = 1
· 使用定理 `Filter.Tendsto.rpow`：Filter.Tendsto.rpow {l : Filter α} {f g : α -> Real
} {x y : Real} (hf : Tendsto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) (h : x != 0 ∨ 0
 < y) : T…
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
-/
theorem Filter.Tendsto.rpow_const {l : Filter α} {f : α → ℝ} {x p : ℝ} (hf : Tendsto f l (𝓝 x))
    (h : x ≠ 0 ∨ 0 ≤ p) : Tendsto (fun a => f a ^ p) l (𝓝 (x ^ p)) :=
  if h0 : 0 = p then h0 ▸ by simp [tendsto_const_nhds]
  else hf.rpow tendsto_const_nhds (h.imp id fun h' => h'.lt_of_ne h0)
/-
**Filter.Tendsto.rpow_const_nhds_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.rpow_const_nhds_zero {l : Filter α} {f : α -> Real} {p : Re
al} (hf : Tendsto f l (𝓝 0)) (hp : 0 < p) : Tendsto (fun t => f t ^ p) l (𝓝 0)
参数：hf : Tendsto f l (𝓝 0)；hp : 0 < p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.rpow_const`：Filter.Tendsto.rpow_const {l : Filter α} {f :
 α -> Real} {x p : Real} (hf : Tendsto f l (𝓝 x)) (h : x != 0 ∨ 0 <= p) : Tendst
o (fun a => f a…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.zero_rpow`：zero_rpow {x : Real} (h : x != 0) : (0 : Real) ^ x = 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
theorem Filter.Tendsto.rpow_const_nhds_zero {l : Filter α} {f : α → ℝ} {p : ℝ}
    (hf : Tendsto f l (𝓝 0)) (hp : 0 < p) :
    Tendsto (fun t ↦ f t ^ p) l (𝓝 0) :=
  Real.zero_rpow hp.ne' ▸ hf.rpow_const (.inr hp.le)

variable [TopologicalSpace α] {f g : α → ℝ} {s : Set α} {x : α} {p : ℝ}

nonrec theorem ContinuousAt.rpow (hf : ContinuousAt f x) (hg : ContinuousAt g x)
    (h : f x ≠ 0 ∨ 0 < g x) : ContinuousAt (fun t => f t ^ g t) x :=
  hf.rpow hg h

nonrec theorem ContinuousWithinAt.rpow (hf : ContinuousWithinAt f s x)
    (hg : ContinuousWithinAt g s x) (h : f x ≠ 0 ∨ 0 < g x) :
    ContinuousWithinAt (fun t => f t ^ g t) s x :=
  hf.rpow hg h
/-
**ContinuousOn.rpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.rpow (hf : ContinuousOn f s) (hg : ContinuousOn g s) (h : for
all x in s, f x != 0 ∨ 0 < g x) : ContinuousOn (fun t => f t ^ g t) s
参数：hf : ContinuousOn f s；hg : ContinuousOn g s；h : forall x in s, f x != 0 ∨ 0 <
 g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.rpow`：∀ {α : Type u_1} [inst : TopologicalSpace α] {f
 g : α → ℝ} {s : Set α} {x : α},   ContinuousWithinAt f s x → ContinuousWithinAt
 g s x → f x …
-/
theorem ContinuousOn.rpow (hf : ContinuousOn f s) (hg : ContinuousOn g s)
    (h : ∀ x ∈ s, f x ≠ 0 ∨ 0 < g x) : ContinuousOn (fun t => f t ^ g t) s := fun t ht =>
  (hf t ht).rpow (hg t ht) (h t ht)
/-
**Continuous.rpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.rpow (hf : Continuous f) (hg : Continuous g) (h : forall x, f x
 != 0 ∨ 0 < g x) : Continuous fun x => f x ^ g x
参数：hf : Continuous f；hg : Continuous g；h : forall x, f x != 0 ∨ 0 < g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `ContinuousAt.rpow`：∀ {α : Type u_1} [inst : TopologicalSpace α] {f g : α
 → ℝ} {x : α},   ContinuousAt f x → ContinuousAt g x → f x ≠ 0 ∨ 0 < g x → Conti
nuousAt…
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
-/
theorem Continuous.rpow (hf : Continuous f) (hg : Continuous g) (h : ∀ x, f x ≠ 0 ∨ 0 < g x) :
    Continuous fun x => f x ^ g x :=
  continuous_iff_continuousAt.2 fun x => hf.continuousAt.rpow hg.continuousAt (h x)

nonrec theorem ContinuousWithinAt.rpow_const (hf : ContinuousWithinAt f s x) (h : f x ≠ 0 ∨ 0 ≤ p) :
    ContinuousWithinAt (fun x => f x ^ p) s x :=
  hf.rpow_const h

nonrec theorem ContinuousAt.rpow_const (hf : ContinuousAt f x) (h : f x ≠ 0 ∨ 0 ≤ p) :
    ContinuousAt (fun x => f x ^ p) x :=
  hf.rpow_const h
/-
**ContinuousOn.rpow_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.rpow_const (hf : ContinuousOn f s) (h : forall x in s, f x !=
 0 ∨ 0 <= p) : ContinuousOn (fun x => f x ^ p) s
参数：hf : ContinuousOn f s；h : forall x in s, f x != 0 ∨ 0 <= p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.rpow_const`：∀ {α : Type u_1} [inst : TopologicalSpace
 α] {f : α → ℝ} {s : Set α} {x : α} {p : ℝ},   ContinuousWithinAt f s x → f x ≠ 
0 ∨ 0 ≤ p → Continu…
-/
theorem ContinuousOn.rpow_const (hf : ContinuousOn f s) (h : ∀ x ∈ s, f x ≠ 0 ∨ 0 ≤ p) :
    ContinuousOn (fun x => f x ^ p) s := fun x hx => (hf x hx).rpow_const (h x hx)
/-
**Continuous.rpow_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.rpow_const (hf : Continuous f) (h : forall x, f x != 0 ∨ 0 <= p
) : Continuous fun x => f x ^ p
参数：hf : Continuous f；h : forall x, f x != 0 ∨ 0 <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `ContinuousAt.rpow_const`：∀ {α : Type u_1} [inst : TopologicalSpace α] {f
 : α → ℝ} {x : α} {p : ℝ},   ContinuousAt f x → f x ≠ 0 ∨ 0 ≤ p → ContinuousAt (
fun x => f x …
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
-/
theorem Continuous.rpow_const (hf : Continuous f) (h : ∀ x, f x ≠ 0 ∨ 0 ≤ p) :
    Continuous fun x => f x ^ p :=
  continuous_iff_continuousAt.2 fun x => hf.continuousAt.rpow_const (h x)

end

end RpowLimits

/-! ## Continuity results for `cpow`, part II

These results involve relating real and complex powers, so cannot be done higher up.
-/


section CpowLimits2

namespace Complex

/-- See also `continuousAt_cpow` and `Complex.continuousAt_cpow_of_re_pos`. -/
/-
**Complex.continuousAt_cpow_zero_of_re_pos** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：continuousAt_cpow_zero_of_re_pos {z : Complex} (hz : 0 < z.re) : Continuou
sAt (fun x : Complex × Complex => x.1 ^ x.2) (0, z)
参数：hz : 0 < z.re。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousAt.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSp
ace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (x : X),   ContinuousAt f x = F
ilter.T…
· 使用定理 `Complex.zero_cpow`：zero_cpow {x : Complex} (h : x != 0) : (0 : Complex) 
^ x = 0
· 使用定理 `tendsto_zero_iff_norm_tendsto_zero`：∀ {α : Type u_1} {E : Type u_4} [ins
t : SeminormedAddGroup E] {f : α → E} {a : Filter α},   Filter.Tendsto f a (nhds
 0) ↔ Filter.Tendsto (fu…
· 使用引理 `squeeze_zero`：squeeze_zero {α} {f g : α -> Real} {t₀ : Filter α} (hf : f
orall t, 0 <= f t) (hft : forall t, f t <= g t) (g0 : Tendsto g t₀ (𝓝 0)) : Tend
st…
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Complex.norm_cpow_le`：norm_cpow_le (z w : Complex) : ‖z ^ w‖ <= ‖z‖ ^ w.
re / Real.exp (arg z * im w)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Filter.Tendsto.zero_mul_isBoundedUnder_le`：Filter.Tendsto.zero_mul_isBou
ndedUnder_le {f g : ι -> α} {l : Filter ι} (hf : Tendsto f l (𝓝 0)) (hg : IsBoun
dedUnder (· <= ·) l ((‖·‖) ∘ g)…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `Real.zero_rpow`：zero_rpow {x : Real} (h : x != 0) : (0 : Real) ^ x = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.Tendsto.rpow`：Filter.Tendsto.rpow {l : Filter α} {f g : α -> Real
} {x y : Real} (hf : Tendsto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) (h : x != 0 ∨ 0
 < y) : T…
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `Continuous.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedAddGr
oup E] [inst_1 : TopologicalSpace α] {f : α → E},   Continuous f → Continuous fu
n x =…
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Complex.continuous_re`：Continuous Complex.re
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
（共 58 条，此处仅展示前 30 条）

--- 原说明 ---
See also `continuousAt_cpow` and `Complex.continuousAt_cpow_of_re_pos`.
-/
theorem continuousAt_cpow_zero_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    ContinuousAt (fun x : ℂ × ℂ => x.1 ^ x.2) (0, z) := by
  have hz₀ : z ≠ 0 := ne_of_apply_ne re hz.ne'
  rw [ContinuousAt, zero_cpow hz₀, tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun _ => norm_cpow_le _ _) ?_
  simp only [div_eq_mul_inv, ← Real.exp_neg]
  refine Tendsto.zero_mul_isBoundedUnder_le ?_ ?_
  · convert!
    (continuous_fst.norm.tendsto ((0 : ℂ), z)).rpow ((continuous_re.comp continuous_snd).tendsto _)
      _ <;>
      simp [hz, Real.zero_rpow hz.ne']
  · simp only [Function.comp_def, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rcases exists_gt |im z| with ⟨C, hC⟩
    refine ⟨Real.exp (π * C), eventually_map.2 ?_⟩
    refine
      (((continuous_im.comp continuous_snd).abs.tendsto (_, z)).eventually (gt_mem_nhds hC)).mono
        fun z hz => Real.exp_le_exp.2 <| (neg_le_abs _).trans ?_
    rw [_root_.abs_mul]
    exact
      mul_le_mul (abs_le.2 ⟨(neg_pi_lt_arg _).le, arg_le_pi _⟩) hz.le (_root_.abs_nonneg _)
        Real.pi_pos.le

open ComplexOrder in
/-- See also `continuousAt_cpow` for a version that assumes `p.1 ≠ 0` but makes no
assumptions about `p.2`. -/
/-
**Complex.continuousAt_cpow_of_re_pos** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：continuousAt_cpow_of_re_pos {p : Complex × Complex} (h₁ : 0 <= p.1.re ∨ p.
1.im != 0) (h₂ : 0 < p.2.re) : ContinuousAt (fun x : Complex × Complex => x.1 ^ 
x.2) p
参数：h₁ : 0 <= p.1.re ∨ p.1.im != 0；h₂ : 0 < p.2.re。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.not_le_zero_iff`：not_le_zero_iff {z : Complex} : ¬z <= 0 ↔ 0 < z
.re ∨ z.im != 0
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `not_and_or`：not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b
· 使用定理 `lt_iff_le_and_ne`：lt_iff_le_and_ne : a < b ↔ a <= b ∧ a != b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.not_lt_zero_iff`：not_lt_zero_iff {z : Complex} : ¬z < 0 ↔ 0 <= z
.re ∨ z.im != 0
· 使用定理 `continuousAt_cpow`：continuousAt_cpow {p : Complex × Complex} (hp_fst : p
.fst in slitPlane) : ContinuousAt (fun x : Complex × Complex => x.1 ^ x.2) p
· 使用定理 `Complex.continuousAt_cpow_zero_of_re_pos`：continuousAt_cpow_zero_of_re_p
os {z : Complex} (hz : 0 < z.re) : ContinuousAt (fun x : Complex × Complex => x.
1 ^ x.2) (0, z)

--- 原说明 ---
See also `continuousAt_cpow` for a version that assumes `p.1 ≠ 0` but makes no
assumptions about `p.2`.
-/
theorem continuousAt_cpow_of_re_pos {p : ℂ × ℂ} (h₁ : 0 ≤ p.1.re ∨ p.1.im ≠ 0) (h₂ : 0 < p.2.re) :
    ContinuousAt (fun x : ℂ × ℂ => x.1 ^ x.2) p := by
  obtain ⟨z, w⟩ := p
  rw [← not_lt_zero_iff, lt_iff_le_and_ne, not_and_or, Ne, Classical.not_not,
    not_le_zero_iff] at h₁
  rcases h₁ with (h₁ | (rfl : z = 0))
  exacts [continuousAt_cpow h₁, continuousAt_cpow_zero_of_re_pos h₂]

/-- See also `continuousAt_cpow_const` for a version that assumes `z ≠ 0` but makes no
assumptions about `w`. -/
/-
**Complex.continuousAt_cpow_const_of_re_pos** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：continuousAt_cpow_const_of_re_pos {z w : Complex} (hz : 0 <= re z ∨ im z !
= 0) (hw : 0 < re w) : ContinuousAt (fun x => x ^ w) z
参数：hz : 0 <= re z ∨ im z != 0；hw : 0 < re w。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Complex.continuousAt_cpow_of_re_pos`：continuousAt_cpow_of_re_pos {p : Co
mplex × Complex} (h₁ : 0 <= p.1.re ∨ p.1.im != 0) (h₂ : 0 < p.2.re) : Continuous
At (fun x : Complex × Com…
· 使用定理 `ContinuousAt.prodMk`：ContinuousAt.prodMk {f : X -> Y} {g : X -> Z} {x : 
X} (hf : ContinuousAt f x) (hg : ContinuousAt g x) : ContinuousAt (fun x => (f x
, g x)) x
· 使用定理 `continuousAt_id`：continuousAt_id : ContinuousAt id x
· 使用定理 `continuousAt_const`：continuousAt_const : ContinuousAt (fun _ : X => y) x

--- 原说明 ---
See also `continuousAt_cpow_const` for a version that assumes `z ≠ 0` but makes 
no
assumptions about `w`.
-/
theorem continuousAt_cpow_const_of_re_pos {z w : ℂ} (hz : 0 ≤ re z ∨ im z ≠ 0) (hw : 0 < re w) :
    ContinuousAt (fun x => x ^ w) z :=
  Tendsto.comp (@continuousAt_cpow_of_re_pos (z, w) hz hw)
    (continuousAt_id.prodMk continuousAt_const)

/-- Continuity of `(x, y) ↦ x ^ y` as a function on `ℝ × ℂ`. -/
/-
**Complex.continuousAt_ofReal_cpow** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：continuousAt_ofReal_cpow (x : Real) (y : Complex) (h : 0 < y.re ∨ x != 0) 
: ContinuousAt (fun p => (p.1 : Complex) ^ p.2 : Real × Complex -> Complex) (x, 
y)
参数：x : Real；y : Complex；h : 0 < y.re ∨ x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `ContinuousAt.prodMk`：ContinuousAt.prodMk {f : X -> Y} {g : X -> Z} {x : 
X} (hf : ContinuousAt f x) (hg : ContinuousAt g x) : ContinuousAt (fun x => (f x
, g x)) x
· 使用定理 `ContinuousAt.comp'`：ContinuousAt.comp' {g : Y -> Z} {x : X} (hg : Contin
uousAt g (f x)) (hf : ContinuousAt f x) : ContinuousAt (fun x => g (f x)) x
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `Complex.continuous_ofReal`：Continuous Complex.ofReal
· 使用定理 `ContinuousAt.fst`：ContinuousAt.fst {f : X -> Y × Z} {x : X} (hf : Contin
uousAt f x) : ContinuousAt (fun x : X => (f x).1) x
· 使用定理 `continuousAt_id'`：continuousAt_id' (y) : ContinuousAt (fun x : X => x) y
· 使用定理 `ContinuousAt.snd`：ContinuousAt.snd {f : X -> Y × Z} {x : X} (hf : Contin
uousAt f x) : ContinuousAt (fun x : X => (f x).2) x
· 使用定理 `ContinuousAt.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace
 Z] {f …
· 使用定理 `continuousAt_cpow`：continuousAt_cpow {p : Complex × Complex} (hp_fst : p
.fst in slitPlane) : ContinuousAt (fun x : Complex × Complex => x.1 ^ x.2) p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.ofReal_re`：ofReal_re (r : Real) : Complex.re (r : Complex) = r
· 使用定理 `Complex.ofReal_zero`：ofReal_zero : ((0 : Real) : Complex) = 0
· 使用定理 `Complex.continuousAt_cpow_zero_of_re_pos`：continuousAt_cpow_zero_of_re_p
os {z : Complex} (hz : 0 < z.re) : ContinuousAt (fun x : Complex × Complex => x.
1 ^ x.2) (0, z)
· 使用定理 `ContinuousAt.comp_of_eq`：ContinuousAt.comp_of_eq {g : Y -> Z} (hg : Cont
inuousAt g y) (hf : ContinuousAt f x) (hy : f x = y) : ContinuousAt (g ∘ f) x
· 使用定理 `ContinuousAt.fun_neg`：∀ {G : Type u_1} {X : Type u_3} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace G] [inst_2 : Neg G]   [ContinuousNeg G] {f 
: X → G} {…
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `ContinuousAt.mul`：ContinuousAt.mul (hf : ContinuousAt f x) (hg : Continu
ousAt g x) : ContinuousAt (f * g) x
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `Complex.neg_re`：neg_re (z : Complex) : (-z).re = -z.re
· 使用定理 `neg_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeftStri
ctMono α] {a : α}, 0 < -a ↔ a < 0
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ContinuousAt.cexp`：ContinuousAt.cexp (h : ContinuousAt f x) : Continuous
At (fun y => exp (f y)) x
（共 45 条，此处仅展示前 30 条）

--- 原说明 ---
Continuity of `(x, y) ↦ x ^ y` as a function on `ℝ × ℂ`.
-/
theorem continuousAt_ofReal_cpow (x : ℝ) (y : ℂ) (h : 0 < y.re ∨ x ≠ 0) :
    ContinuousAt (fun p => (p.1 : ℂ) ^ p.2 : ℝ × ℂ → ℂ) (x, y) := by
  rcases lt_trichotomy (0 : ℝ) x with (hx | rfl | hx)
  · -- x > 0 : easy case
    have : ContinuousAt (fun p => ⟨↑p.1, p.2⟩ : ℝ × ℂ → ℂ × ℂ) (x, y) := by fun_prop
    refine (continuousAt_cpow (Or.inl ?_)).comp this
    rwa [ofReal_re]
  · -- x = 0 : reduce to continuousAt_cpow_zero_of_re_pos
    have A : ContinuousAt (fun p => p.1 ^ p.2 : ℂ × ℂ → ℂ) ⟨↑(0 : ℝ), y⟩ := by
      rw [ofReal_zero]
      apply continuousAt_cpow_zero_of_re_pos
      tauto
    have B : ContinuousAt (fun p => ⟨↑p.1, p.2⟩ : ℝ × ℂ → ℂ × ℂ) ⟨0, y⟩ := by fun_prop
    exact A.comp_of_eq B rfl
  · -- x < 0 : difficult case
    suffices ContinuousAt (fun p => (-(p.1 : ℂ)) ^ p.2 * exp (π * I * p.2) : ℝ × ℂ → ℂ) (x, y) by
      refine this.congr (eventually_of_mem (prod_mem_nhds (Iio_mem_nhds hx) univ_mem) ?_)
      exact fun p hp => (ofReal_cpow_of_nonpos (le_of_lt hp.1) p.2).symm
    have A : ContinuousAt (fun p => ⟨-↑p.1, p.2⟩ : ℝ × ℂ → ℂ × ℂ) (x, y) := by fun_prop
    apply ContinuousAt.mul
    · refine (continuousAt_cpow (Or.inl ?_)).comp A
      rwa [neg_re, ofReal_re, neg_pos]
    · fun_prop
/-
**Complex.continuousAt_ofReal_cpow_const** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：continuousAt_ofReal_cpow_const (x : Real) (y : Complex) (h : 0 < y.re ∨ x 
!= 0) : ContinuousAt (fun a => (a : Complex) ^ y : Real -> Complex) x
参数：x : Real；y : Complex；h : 0 < y.re ∨ x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.comp₂_of_eq`：ContinuousAt.comp₂_of_eq {f : Y × Z -> W} {g :
 X -> Y} {h : X -> Z} {x : X} {y : Y × Z} (hf : ContinuousAt f y) (hg : Continuo
usAt g x) (hh …
· 使用定理 `Complex.continuousAt_ofReal_cpow`：continuousAt_ofReal_cpow (x : Real) (y
 : Complex) (h : 0 < y.re ∨ x != 0) : ContinuousAt (fun p => (p.1 : Complex) ^ p
.2 : Real × Complex ->…
· 使用定理 `continuousAt_id'`：continuousAt_id' (y) : ContinuousAt (fun x : X => x) y
· 使用定理 `continuousAt_const`：continuousAt_const : ContinuousAt (fun _ : X => y) x
-/
theorem continuousAt_ofReal_cpow_const (x : ℝ) (y : ℂ) (h : 0 < y.re ∨ x ≠ 0) :
    ContinuousAt (fun a => (a : ℂ) ^ y : ℝ → ℂ) x :=
  (continuousAt_ofReal_cpow x y h).comp₂_of_eq (by fun_prop) (by fun_prop) rfl
/-
**Complex.continuous_ofReal_cpow_const** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：continuous_ofReal_cpow_const {y : Complex} (hs : 0 < y.re) : Continuous (f
un x => (x : Complex) ^ y : Real -> Complex)
参数：hs : 0 < y.re。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `Complex.continuousAt_ofReal_cpow_const`：continuousAt_ofReal_cpow_const (
x : Real) (y : Complex) (h : 0 < y.re ∨ x != 0) : ContinuousAt (fun a => (a : Co
mplex) ^ y : Real -> Complex…
-/
theorem continuous_ofReal_cpow_const {y : ℂ} (hs : 0 < y.re) :
    Continuous (fun x => (x : ℂ) ^ y : ℝ → ℂ) :=
  continuous_iff_continuousAt.mpr fun x => continuousAt_ofReal_cpow_const x y (Or.inl hs)

end Complex

end CpowLimits2

/-! ## Limits and continuity for `ℝ≥0` powers -/


namespace NNReal

/-
**NNReal.continuousAt_rpow** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：continuousAt_rpow {x : Real>=0} {y : Real} (h : x != 0 ∨ 0 < y) : Continuo
usAt (fun p : Real>=0 × Real => p.1 ^ p.2) (x, y)
参数：h : x != 0 ∨ 0 < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `Real.rpow_nonneg`：rpow_nonneg {x : Real} (hx : 0 <= x) (y : Real) : 0 <=
 x ^ y
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousAt.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace
 Z] {f …
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `continuous_real_toNNReal`：Continuous Real.toNNReal
· 使用定理 `Real.continuousAt_rpow`：continuousAt_rpow (p : Real × Real) (h : p.1 != 
0 ∨ 0 < p.2) : ContinuousAt (fun p : Real × Real => p.1 ^ p.2) p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ContinuousAt.prodMk`：ContinuousAt.prodMk {f : X -> Y} {g : X -> Z} {x : 
X} (hf : ContinuousAt f x) (hg : ContinuousAt g x) : ContinuousAt (fun x => (f x
, g x)) x
· 使用定理 `ContinuousAt.comp'`：ContinuousAt.comp' {g : Y -> Z} {x : X} (hg : Contin
uousAt g (f x)) (hf : ContinuousAt f x) : ContinuousAt (fun x => g (f x)) x
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `ContinuousAt.fst`：ContinuousAt.fst {f : X -> Y × Z} {x : X} (hf : Contin
uousAt f x) : ContinuousAt (fun x : X => (f x).1) x
· 使用定理 `continuousAt_id'`：continuousAt_id' (y) : ContinuousAt (fun x : X => x) y
· 使用定理 `ContinuousAt.snd`：ContinuousAt.snd {f : X -> Y × Z} {x : X} (hf : Contin
uousAt f x) : ContinuousAt (fun x : X => (f x).2) x
-/
theorem continuousAt_rpow {x : ℝ≥0} {y : ℝ} (h : x ≠ 0 ∨ 0 < y) :
    ContinuousAt (fun p : ℝ≥0 × ℝ => p.1 ^ p.2) (x, y) := by
  have :
    (fun p : ℝ≥0 × ℝ => p.1 ^ p.2) =
      Real.toNNReal ∘ (fun p : ℝ × ℝ => p.1 ^ p.2) ∘ fun p : ℝ≥0 × ℝ => (p.1.1, p.2) := by
    ext p
    simp only [coe_rpow, val_eq_coe, Function.comp_apply, coe_toNNReal', left_eq_sup]
    positivity
  rw [this]
  refine continuous_real_toNNReal.continuousAt.comp (ContinuousAt.comp ?_ ?_)
  · apply Real.continuousAt_rpow
    simpa using h
  · fun_prop
/-
**NNReal.eventually_pow_one_div_le** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：eventually_pow_one_div_le (x : Real>=0) {y : Real>=0} (hy : 1 < y) : foral
lᶠ n : Nat in atTop, x ^ (1 / n : Real) <= y
参数：x : Real>=0；hy : 1 < y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_one_pow_unbounded_of_pos`：add_one_pow_unbounded_of_pos (x : R) (hy :
 0 < y) : exists n : Nat, x < (y + 1) ^ n
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `NNReal.instArchimedean`：Archimedean NNReal
· 使用定理 `tsub_pos_of_lt`：tsub_pos_of_lt (h : a < b) : 0 < b - a
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
· 使用定理 `NNReal.instOrderedSub`：OrderedSub NNReal
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NNReal.rpow_inv_le_iff`：rpow_inv_le_iff {x y : Real>=0} {z : Real} (hz :
 0 < z) : x ^ z⁻¹ <= y ↔ x <= y ^ z
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用引理 `NNReal.rpow_natCast`：rpow_natCast (x : Real>=0) (n : Nat) : x ^ (n : Rea
l) = x ^ n
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用引理 `pow_right_mono₀`：pow_right_mono₀ [ZeroLEOneClass M₀] [PosMulMono M₀] (h 
: 1 <= a) : Monotone (a ^ ·)
· 使用定理 `FloorSemiring.instZeroLEOneClass`：∀ {α : Type u_2} [inst : Semiring α] [
inst_1 : PartialOrder α] [FloorSemiring α], ZeroLEOneClass α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `NNReal.instIsOrderedRing_1`：IsOrderedRing NNReal
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
-/
theorem eventually_pow_one_div_le (x : ℝ≥0) {y : ℝ≥0} (hy : 1 < y) :
    ∀ᶠ n : ℕ in atTop, x ^ (1 / n : ℝ) ≤ y := by
  obtain ⟨m, hm⟩ := add_one_pow_unbounded_of_pos x (tsub_pos_of_lt hy)
  rw [tsub_add_cancel_of_le hy.le] at hm
  refine eventually_atTop.2 ⟨m + 1, fun n hn => ?_⟩
  simp only [one_div]
  simpa only [NNReal.rpow_inv_le_iff (Nat.cast_pos.2 <| m.succ_pos.trans_le hn),
    NNReal.rpow_natCast] using hm.le.trans (pow_right_mono₀ hy.le (m.le_succ.trans hn))

end NNReal

open Filter

/-
**Filter.Tendsto.nnrpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.nnrpow {α : Type*} {f : Filter α} {u : α -> Real>=0} {v : α
 -> Real} {x : Real>=0} {y : Real} (hx : Tendsto u f (𝓝 x)) (hy : Tendsto v f (𝓝
 y)) (h : x != 0 ∨ 0 < y) : Tendsto (fun a => u a ^ v a) f (𝓝 (x ^ y))
参数：hx : Tendsto u f (𝓝 x)；hy : Tendsto v f (𝓝 y)；h : x != 0 ∨ 0 < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `NNReal.continuousAt_rpow`：continuousAt_rpow {x : Real>=0} {y : Real} (h 
: x != 0 ∨ 0 < y) : ContinuousAt (fun p : Real>=0 × Real => p.1 ^ p.2) (x, y)
· 使用定理 `Filter.Tendsto.prodMk_nhds`：Filter.Tendsto.prodMk_nhds {γ} {x : X} {y : 
Y} {f : Filter γ} {mx : γ -> X} {my : γ -> Y} (hx : Tendsto mx f (𝓝 x)) (hy : Te
ndsto my f (𝓝 y)…
-/
theorem Filter.Tendsto.nnrpow {α : Type*} {f : Filter α} {u : α → ℝ≥0} {v : α → ℝ} {x : ℝ≥0}
    {y : ℝ} (hx : Tendsto u f (𝓝 x)) (hy : Tendsto v f (𝓝 y)) (h : x ≠ 0 ∨ 0 < y) :
    Tendsto (fun a => u a ^ v a) f (𝓝 (x ^ y)) :=
  Tendsto.comp (NNReal.continuousAt_rpow h) (hx.prodMk_nhds hy)

namespace NNReal

/-
**NNReal.continuousAt_rpow_const** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：continuousAt_rpow_const {x : Real>=0} {y : Real} (h : x != 0 ∨ 0 <= y) : C
ontinuousAt (fun z => z ^ y) x
参数：h : x != 0 ∨ 0 <= y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Filter.Tendsto.nnrpow`：Filter.Tendsto.nnrpow {α : Type*} {f : Filter α} 
{u : α -> Real>=0} {v : α -> Real} {x : Real>=0} {y : Real} (hx : Tendsto u f (𝓝
 x)) (hy : …
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NNReal.rpow_zero`：rpow_zero (x : Real>=0) : x ^ (0 : Real) = 1
-/
theorem continuousAt_rpow_const {x : ℝ≥0} {y : ℝ} (h : x ≠ 0 ∨ 0 ≤ y) :
    ContinuousAt (fun z => z ^ y) x :=
  h.elim (fun h => tendsto_id.nnrpow tendsto_const_nhds (Or.inl h)) fun h =>
    h.eq_or_lt.elim (fun h => h ▸ by simp only [rpow_zero, continuousAt_const]) fun h =>
      tendsto_id.nnrpow tendsto_const_nhds (Or.inr h)

@[fun_prop]
/-
**NNReal.continuous_rpow_const** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：continuous_rpow_const {y : Real} (h : 0 <= y) : Continuous fun x : Real>=0
 => x ^ y
参数：h : 0 <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `NNReal.continuousAt_rpow_const`：continuousAt_rpow_const {x : Real>=0} {y
 : Real} (h : x != 0 ∨ 0 <= y) : ContinuousAt (fun z => z ^ y) x
-/
theorem continuous_rpow_const {y : ℝ} (h : 0 ≤ y) : Continuous fun x : ℝ≥0 => x ^ y :=
  continuous_iff_continuousAt.2 fun _ => continuousAt_rpow_const (Or.inr h)

@[fun_prop]
/-
**NNReal.continuousOn_rpow_const_compl_zero** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：continuousOn_rpow_const_compl_zero {r : Real} : ContinuousOn (fun z : Real
>=0 => z ^ r) {0}ᶜ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `NNReal.continuousAt_rpow_const`：continuousAt_rpow_const {x : Real>=0} {y
 : Real} (h : x != 0 ∨ 0 <= y) : ContinuousAt (fun z => z ^ y) x
-/
theorem continuousOn_rpow_const_compl_zero {r : ℝ} :
    ContinuousOn (fun z : ℝ≥0 => z ^ r) {0}ᶜ :=
  fun _ h => ContinuousAt.continuousWithinAt <| NNReal.continuousAt_rpow_const (.inl h)

-- even though this follows from `ContinuousOn.mono` and the previous lemma, we include it for
-- automation purposes with `fun_prop`, because the side goal `0 ∉ s ∨ 0 ≤ r` is often easy to check
@[fun_prop]
/-
**NNReal.continuousOn_rpow_const** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：continuousOn_rpow_const {r : Real} {s : Set Real>=0} (h : 0 ∉ s ∨ 0 <= r) 
: ContinuousOn (fun z : Real>=0 => z ^ r) s
参数：h : 0 ∉ s ∨ 0 <= r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `NNReal.continuousOn_rpow_const_compl_zero`：continuousOn_rpow_const_compl
_zero {r : Real} : ContinuousOn (fun z : Real>=0 => z ^ r) {0}ᶜ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `NNReal.continuous_rpow_const`：continuous_rpow_const {y : Real} (h : 0 <=
 y) : Continuous fun x : Real>=0 => x ^ y
-/
theorem continuousOn_rpow_const {r : ℝ} {s : Set ℝ≥0}
    (h : 0 ∉ s ∨ 0 ≤ r) : ContinuousOn (fun z : ℝ≥0 => z ^ r) s :=
  h.elim (fun _ ↦ ContinuousOn.mono (s := {0}ᶜ) (by fun_prop) (by simp_all))
    (NNReal.continuous_rpow_const · |>.continuousOn)

end NNReal

/-! ## Continuity for `ℝ≥0∞` powers -/


namespace ENNReal

/-
**ENNReal.eventually_pow_one_div_le** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：eventually_pow_one_div_le {x : Real>=0∞} (hx : x != ∞) {y : Real>=0∞} (hy 
: 1 < y) : forallᶠ n : Nat in atTop, x ^ (1 / n : Real) <= y
参数：hx : x != ∞；hy : 1 < y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.eventually_pow_one_div_le`：eventually_pow_one_div_le (x : Real>=0
) {y : Real>=0} (hy : 1 < y) : forallᶠ n : Nat in atTop, x ^ (1 / n : Real) <= y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Filter.Eventually.congr`：∀ {α : Type u} {f : Filter α} {p q : α → Prop},
   (∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x ↔ q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `ENNReal.coe_rpow_of_nonneg`：coe_rpow_of_nonneg (x : Real>=0) {y : Real} 
(h : 0 <= y) : ↑(x ^ y) = (x : Real>=0∞) ^ y
· 使用引理 `Mathlib.Meta.Positivity.div_nonneg_of_pos_of_nonneg`：div_nonneg_of_pos_o
f_nonneg [PosMulReflectLT α] (ha : 0 < a) (hb : 0 <= b) : 0 <= a / b
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
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.coe_le_coe`：∀ {r q : NNReal}, ↑r ≤ ↑q ↔ r ≤ q
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem eventually_pow_one_div_le {x : ℝ≥0∞} (hx : x ≠ ∞) {y : ℝ≥0∞} (hy : 1 < y) :
    ∀ᶠ n : ℕ in atTop, x ^ (1 / n : ℝ) ≤ y := by
  lift x to ℝ≥0 using hx
  by_cases h : y = ∞
  · exact Eventually.of_forall fun n => h.symm ▸ le_top
  · lift y to ℝ≥0 using h
    have := NNReal.eventually_pow_one_div_le x (mod_cast hy : 1 < y)
    refine this.congr (Eventually.of_forall fun n => ?_)
    rw [← coe_rpow_of_nonneg x (by positivity : 0 ≤ (1 / n : ℝ)), coe_le_coe]
/-
**ENNReal.continuousAt_rpow_const_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem continuousAt_rpow_const_of_pos {x : ℝ≥0∞} {y : ℝ} (h : 0 < y) :
    ContinuousAt (fun a : ℝ≥0∞ => a ^ y) x := by
  by_cases hx : x = ⊤
  · rw [hx, ContinuousAt]
    convert! ENNReal.tendsto_rpow_at_top h
    simp [h]
  lift x to ℝ≥0 using hx
  rw [continuousAt_coe_iff]
  convert! continuous_coe.continuousAt.comp (NNReal.continuousAt_rpow_const (Or.inr h.le)) using 1
  ext1 x
  simp [← coe_rpow_of_nonneg _ h.le]

@[continuity, fun_prop]
/-
**ENNReal.continuous_rpow_const** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：continuous_rpow_const {y : Real} : Continuous fun a : Real>=0∞ => a ^ y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `_private.Mathlib.Analysis.SpecialFunctions.Pow.Continuity.0.ENNReal.cont
inuousAt_rpow_const_of_pos`：∀ {x : ENNReal} {y : ℝ}, 0 < y → ContinuousAt (fun a
 => a ^ y) x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ENNReal.rpow_zero`：rpow_zero {x : Real>=0∞} : x ^ (0 : Real) = 1
· 使用定理 `continuousAt_const`：continuousAt_const : ContinuousAt (fun _ : X => y) x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
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
· 使用定理 `ENNReal.rpow_neg`：rpow_neg (x : Real>=0∞) (y : Real) : x ^ (-y) = (x ^ y
)⁻¹
· 使用定理 `ContinuousAt.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace
 Z] {f …
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `ContinuousInv.continuous_inv`：∀ {G : Type u} {inst : TopologicalSpace G}
 {inst_1 : Inv G} [self : ContinuousInv G], Continuous fun a => a⁻¹
· 使用定理 `ENNReal.instContinuousInv`：ContinuousInv ENNReal
-/
theorem continuous_rpow_const {y : ℝ} : Continuous fun a : ℝ≥0∞ => a ^ y := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  rcases lt_trichotomy (0 : ℝ) y with (hy | rfl | hy)
  · exact continuousAt_rpow_const_of_pos hy
  · simp only [rpow_zero]
    exact continuousAt_const
  · obtain ⟨z, hz⟩ : ∃ z, y = -z := ⟨-y, (neg_neg _).symm⟩
    have z_pos : 0 < z := by simpa [hz] using hy
    simp_rw [hz, rpow_neg]
    exact continuous_inv.continuousAt.comp (continuousAt_rpow_const_of_pos z_pos)
/-
**ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `ENN
Real`。
形式化陈述：tendsto_const_mul_rpow_nhds_zero_of_pos {c : Real>=0∞} (hc : c != ∞) {y : 
Real} (hy : 0 < y) : Tendsto (fun x : Real>=0∞ => c * x ^ y) (𝓝 0) (𝓝 0)
参数：hc : c != ∞；hy : 0 < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.zero_rpow_of_pos`：zero_rpow_of_pos {y : Real} (h : 0 < y) : (0 :
 Real>=0∞) ^ y = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ENNReal.Tendsto.const_mul`：∀ {α : Type u_1} {f : Filter α} {m : α → ENNR
eal} {a b : ENNReal},   Filter.Tendsto m f (nhds b) → b ≠ 0 ∨ a ≠ ⊤ → Filter.Ten
dsto (fun b => …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `ENNReal.continuous_rpow_const`：continuous_rpow_const {y : Real} : Contin
uous fun a : Real>=0∞ => a ^ y
-/
theorem tendsto_const_mul_rpow_nhds_zero_of_pos {c : ℝ≥0∞} (hc : c ≠ ∞) {y : ℝ} (hy : 0 < y) :
    Tendsto (fun x : ℝ≥0∞ => c * x ^ y) (𝓝 0) (𝓝 0) := by
  convert! ENNReal.Tendsto.const_mul (ENNReal.continuous_rpow_const.tendsto 0) _
  · simp [hy]
  · exact Or.inr hc

end ENNReal

/-
**Filter.Tendsto.ennrpow_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.ennrpow_const {α : Type*} {f : Filter α} {m : α -> Real>=0∞
} {a : Real>=0∞} (r : Real) (hm : Tendsto m f (𝓝 a)) : Tendsto (fun x => m x ^ r
) f (𝓝 (a ^ r))
参数：r : Real；hm : Tendsto m f (𝓝 a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `ENNReal.continuous_rpow_const`：continuous_rpow_const {y : Real} : Contin
uous fun a : Real>=0∞ => a ^ y
-/
theorem Filter.Tendsto.ennrpow_const {α : Type*} {f : Filter α} {m : α → ℝ≥0∞} {a : ℝ≥0∞} (r : ℝ)
    (hm : Tendsto m f (𝓝 a)) : Tendsto (fun x => m x ^ r) f (𝓝 (a ^ r)) :=
  (ENNReal.continuous_rpow_const.tendsto a).comp hm
