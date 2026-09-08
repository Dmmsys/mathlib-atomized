/-
Copyright (c) 2023 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Analytic.CPolynomialDef

/-! # Properties of continuously polynomial functions

We expand the API around continuously polynomial functions. Notably, we show that this class is
stable under the usual operations (addition, subtraction, negation).

We also prove that continuous multilinear maps are continuously polynomial, and so
are continuous linear maps into continuous multilinear maps. In particular, such maps are
analytic.
-/

@[expose] public section

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]

open scoped Topology
open Set Filter Asymptotics NNReal ENNReal

variable {f g : E → F} {p pf pg : FormalMultilinearSeries 𝕜 E F} {x : E} {r r' : ℝ≥0∞} {n m : ℕ}

/-
**hasFiniteFPowerSeriesOnBall_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFiniteFPowerSeriesOnBall_const {c : F} {e : E} : HasFiniteFPowerSeriesO
nBall (fun _ => c) (constFormalMultilinearSeries 𝕜 E c) e 1 ⊤
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `hasFPowerSeriesOnBall_const`：hasFPowerSeriesOnBall_const {c : F} {e : E}
 : HasFPowerSeriesOnBall (fun _ => c) (constFormalMultilinearSeries 𝕜 E c) e ⊤
· 使用定理 `constFormalMultilinearSeries_apply_of_nonzero`：constFormalMultilinearSer
ies_apply_of_nonzero [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedA
ddCommGroup F] [NormedSpace 𝕜 E] [N…
· 使用定理 `Nat.ne_zero_of_lt`：∀ {b a : ℕ}, b < a → a ≠ 0
-/
theorem hasFiniteFPowerSeriesOnBall_const {c : F} {e : E} :
    HasFiniteFPowerSeriesOnBall (fun _ => c) (constFormalMultilinearSeries 𝕜 E c) e 1 ⊤ :=
  ⟨hasFPowerSeriesOnBall_const,
    fun _ hn ↦ constFormalMultilinearSeries_apply_of_nonzero (Nat.ne_zero_of_lt hn)⟩
/-
**hasFiniteFPowerSeriesAt_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFiniteFPowerSeriesAt_const {c : F} {e : E} : HasFiniteFPowerSeriesAt (f
un _ => c) (constFormalMultilinearSeries 𝕜 E c) e 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `hasFiniteFPowerSeriesOnBall_const`：hasFiniteFPowerSeriesOnBall_const {c 
: F} {e : E} : HasFiniteFPowerSeriesOnBall (fun _ => c) (constFormalMultilinearS
eries 𝕜 E c) e 1 ⊤
-/
theorem hasFiniteFPowerSeriesAt_const {c : F} {e : E} :
    HasFiniteFPowerSeriesAt (fun _ => c) (constFormalMultilinearSeries 𝕜 E c) e 1 :=
  ⟨⊤, hasFiniteFPowerSeriesOnBall_const⟩
/-
**CPolynomialAt_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CPolynomialAt_const {v : F} : CPolynomialAt 𝕜 (fun _ => v) x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `hasFiniteFPowerSeriesAt_const`：hasFiniteFPowerSeriesAt_const {c : F} {e 
: E} : HasFiniteFPowerSeriesAt (fun _ => c) (constFormalMultilinearSeries 𝕜 E c)
 e 1
-/
theorem CPolynomialAt_const {v : F} : CPolynomialAt 𝕜 (fun _ => v) x :=
  ⟨constFormalMultilinearSeries 𝕜 E v, 1, hasFiniteFPowerSeriesAt_const⟩
/-
**CPolynomialOn_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CPolynomialOn_const {v : F} {s : Set E} : CPolynomialOn 𝕜 (fun _ => v) s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CPolynomialAt_const`：CPolynomialAt_const {v : F} : CPolynomialAt 𝕜 (fun 
_ => v) x
-/
theorem CPolynomialOn_const {v : F} {s : Set E} : CPolynomialOn 𝕜 (fun _ => v) s :=
  fun _ _ => CPolynomialAt_const

set_option backward.isDefEq.respectTransparency false in
/-
**HasFiniteFPowerSeriesOnBall.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFiniteFPowerSeriesOnBall.add (hf : HasFiniteFPowerSeriesOnBall f pf x n
 r) (hg : HasFiniteFPowerSeriesOnBall g pg x m r) : HasFiniteFPowerSeriesOnBall 
(f + g) (pf + pg) x (max n m) r
参数：hf : HasFiniteFPowerSeriesOnBall f pf x n r；hg : HasFiniteFPowerSeriesOnBall 
g pg x m r。
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
· 使用定理 `HasFPowerSeriesOnBall.add`：HasFPowerSeriesOnBall.add (hf : HasFPowerSeri
esOnBall f pf x r) (hg : HasFPowerSeriesOnBall g pg x r) : HasFPowerSeriesOnBall
 (f + g) (pf + …
· 使用定理 `HasFiniteFPowerSeriesOnBall.toHasFPowerSeriesOnBall`：∀ {𝕜 : Type u_1} {E
 : Type u_2} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedA
ddCommGroup E]   [inst_2 : NormedSpace 𝕜 …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.add_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Add 
(M i)] (f g : (i : ι) → M i) (i : ι), (f + g) i = f i + g i
· 使用定理 `HasFiniteFPowerSeriesOnBall.finite`：∀ {𝕜 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   
[inst_2 : NormedSpace 𝕜 …
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem HasFiniteFPowerSeriesOnBall.add (hf : HasFiniteFPowerSeriesOnBall f pf x n r)
    (hg : HasFiniteFPowerSeriesOnBall g pg x m r) :
    HasFiniteFPowerSeriesOnBall (f + g) (pf + pg) x (max n m) r :=
  ⟨hf.1.add hg.1, fun N hN ↦ by
    rw [Pi.add_apply, hf.finite _ ((le_max_left n m).trans hN),
        hg.finite _ ((le_max_right n m).trans hN), zero_add]⟩
/-
**HasFiniteFPowerSeriesAt.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFiniteFPowerSeriesAt.add (hf : HasFiniteFPowerSeriesAt f pf x n) (hg : 
HasFiniteFPowerSeriesAt g pg x m) : HasFiniteFPowerSeriesAt (f + g) (pf + pg) x 
(max n m)
参数：hf : HasFiniteFPowerSeriesAt f pf x n；hg : HasFiniteFPowerSeriesAt g pg x m。
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
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `ENNReal.nhdsGT_zero_neBot`：(nhdsWithin 0 (Set.Ioi 0)).NeBot
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `HasFiniteFPowerSeriesAt.eventually`：∀ {𝕜 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   
[inst_2 : NormedSpace 𝕜 …
· 使用定理 `HasFiniteFPowerSeriesOnBall.add`：HasFiniteFPowerSeriesOnBall.add (hf : H
asFiniteFPowerSeriesOnBall f pf x n r) (hg : HasFiniteFPowerSeriesOnBall g pg x 
m r) : HasFiniteFPowe…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem HasFiniteFPowerSeriesAt.add (hf : HasFiniteFPowerSeriesAt f pf x n)
    (hg : HasFiniteFPowerSeriesAt g pg x m) :
    HasFiniteFPowerSeriesAt (f + g) (pf + pg) x (max n m) := by
  rcases (hf.eventually.and hg.eventually).exists with ⟨r, hr⟩
  exact ⟨r, hr.1.add hr.2⟩
/-
**CPolynomialAt.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CPolynomialAt.add (hf : CPolynomialAt 𝕜 f x) (hg : CPolynomialAt 𝕜 g x) : 
CPolynomialAt 𝕜 (f + g) x
参数：hf : CPolynomialAt 𝕜 f x；hg : CPolynomialAt 𝕜 g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFiniteFPowerSeriesAt.cpolynomialAt`：HasFiniteFPowerSeriesAt.cpolynomi
alAt (hf : HasFiniteFPowerSeriesAt f p x n) : CPolynomialAt 𝕜 f x
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
· 使用定理 `HasFiniteFPowerSeriesAt.add`：HasFiniteFPowerSeriesAt.add (hf : HasFinite
FPowerSeriesAt f pf x n) (hg : HasFiniteFPowerSeriesAt g pg x m) : HasFiniteFPow
erSeriesAt (f + g…
-/
theorem CPolynomialAt.add (hf : CPolynomialAt 𝕜 f x) (hg : CPolynomialAt 𝕜 g x) :
    CPolynomialAt 𝕜 (f + g) x :=
  let ⟨_, _, hpf⟩ := hf
  let ⟨_, _, hqf⟩ := hg
  (hpf.add hqf).cpolynomialAt

set_option backward.isDefEq.respectTransparency false in
/-
**HasFiniteFPowerSeriesOnBall.neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFiniteFPowerSeriesOnBall.neg (hf : HasFiniteFPowerSeriesOnBall f pf x n
 r) : HasFiniteFPowerSeriesOnBall (-f) (-pf) x n r
参数：hf : HasFiniteFPowerSeriesOnBall f pf x n r。
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
· 使用定理 `HasFPowerSeriesOnBall.neg`：HasFPowerSeriesOnBall.neg (hf : HasFPowerSeri
esOnBall f pf x r) : HasFPowerSeriesOnBall (-f) (-pf) x r
· 使用定理 `HasFiniteFPowerSeriesOnBall.toHasFPowerSeriesOnBall`：∀ {𝕜 : Type u_1} {E
 : Type u_2} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedA
ddCommGroup E]   [inst_2 : NormedSpace 𝕜 …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.neg_apply`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : (i : ι) → Neg 
(G i)] (f : (i : ι) → G i) (i : ι), (-f) i = -f i
· 使用定理 `HasFiniteFPowerSeriesOnBall.finite`：∀ {𝕜 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   
[inst_2 : NormedSpace 𝕜 …
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
-/
theorem HasFiniteFPowerSeriesOnBall.neg (hf : HasFiniteFPowerSeriesOnBall f pf x n r) :
    HasFiniteFPowerSeriesOnBall (-f) (-pf) x n r :=
  ⟨hf.1.neg, fun m hm ↦ by rw [Pi.neg_apply, hf.finite m hm, neg_zero]⟩
/-
**HasFiniteFPowerSeriesAt.neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFiniteFPowerSeriesAt.neg (hf : HasFiniteFPowerSeriesAt f pf x n) : HasF
initeFPowerSeriesAt (-f) (-pf) x n
参数：hf : HasFiniteFPowerSeriesAt f pf x n。
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
· 使用定理 `HasFiniteFPowerSeriesOnBall.hasFiniteFPowerSeriesAt`：HasFiniteFPowerSeri
esOnBall.hasFiniteFPowerSeriesAt (hf : HasFiniteFPowerSeriesOnBall f p x n r) : 
HasFiniteFPowerSeriesAt f p x n
· 使用定理 `HasFiniteFPowerSeriesOnBall.neg`：HasFiniteFPowerSeriesOnBall.neg (hf : H
asFiniteFPowerSeriesOnBall f pf x n r) : HasFiniteFPowerSeriesOnBall (-f) (-pf) 
x n r
-/
theorem HasFiniteFPowerSeriesAt.neg (hf : HasFiniteFPowerSeriesAt f pf x n) :
    HasFiniteFPowerSeriesAt (-f) (-pf) x n :=
  let ⟨_, hrf⟩ := hf
  hrf.neg.hasFiniteFPowerSeriesAt
/-
**CPolynomialAt.neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CPolynomialAt.neg (hf : CPolynomialAt 𝕜 f x) : CPolynomialAt 𝕜 (-f) x
参数：hf : CPolynomialAt 𝕜 f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFiniteFPowerSeriesAt.cpolynomialAt`：HasFiniteFPowerSeriesAt.cpolynomi
alAt (hf : HasFiniteFPowerSeriesAt f p x n) : CPolynomialAt 𝕜 f x
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
· 使用定理 `HasFiniteFPowerSeriesAt.neg`：HasFiniteFPowerSeriesAt.neg (hf : HasFinite
FPowerSeriesAt f pf x n) : HasFiniteFPowerSeriesAt (-f) (-pf) x n
-/
theorem CPolynomialAt.neg (hf : CPolynomialAt 𝕜 f x) : CPolynomialAt 𝕜 (-f) x :=
  let ⟨_, _, hpf⟩ := hf
  hpf.neg.cpolynomialAt
/-
**HasFiniteFPowerSeriesOnBall.sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFiniteFPowerSeriesOnBall.sub (hf : HasFiniteFPowerSeriesOnBall f pf x n
 r) (hg : HasFiniteFPowerSeriesOnBall g pg x m r) : HasFiniteFPowerSeriesOnBall 
(f - g) (pf - pg) x (max n m) r
参数：hf : HasFiniteFPowerSeriesOnBall f pf x n r；hg : HasFiniteFPowerSeriesOnBall 
g pg x m r。
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `HasFiniteFPowerSeriesOnBall.add`：HasFiniteFPowerSeriesOnBall.add (hf : H
asFiniteFPowerSeriesOnBall f pf x n r) (hg : HasFiniteFPowerSeriesOnBall g pg x 
m r) : HasFiniteFPowe…
· 使用定理 `HasFiniteFPowerSeriesOnBall.neg`：HasFiniteFPowerSeriesOnBall.neg (hf : H
asFiniteFPowerSeriesOnBall f pf x n r) : HasFiniteFPowerSeriesOnBall (-f) (-pf) 
x n r
-/
theorem HasFiniteFPowerSeriesOnBall.sub (hf : HasFiniteFPowerSeriesOnBall f pf x n r)
    (hg : HasFiniteFPowerSeriesOnBall g pg x m r) :
    HasFiniteFPowerSeriesOnBall (f - g) (pf - pg) x (max n m) r := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg
/-
**HasFiniteFPowerSeriesAt.sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFiniteFPowerSeriesAt.sub (hf : HasFiniteFPowerSeriesAt f pf x n) (hg : 
HasFiniteFPowerSeriesAt g pg x m) : HasFiniteFPowerSeriesAt (f - g) (pf - pg) x 
(max n m)
参数：hf : HasFiniteFPowerSeriesAt f pf x n；hg : HasFiniteFPowerSeriesAt g pg x m。
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `HasFiniteFPowerSeriesAt.add`：HasFiniteFPowerSeriesAt.add (hf : HasFinite
FPowerSeriesAt f pf x n) (hg : HasFiniteFPowerSeriesAt g pg x m) : HasFiniteFPow
erSeriesAt (f + g…
· 使用定理 `HasFiniteFPowerSeriesAt.neg`：HasFiniteFPowerSeriesAt.neg (hf : HasFinite
FPowerSeriesAt f pf x n) : HasFiniteFPowerSeriesAt (-f) (-pf) x n
-/
theorem HasFiniteFPowerSeriesAt.sub (hf : HasFiniteFPowerSeriesAt f pf x n)
    (hg : HasFiniteFPowerSeriesAt g pg x m) :
    HasFiniteFPowerSeriesAt (f - g) (pf - pg) x (max n m) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg
/-
**CPolynomialAt.sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CPolynomialAt.sub (hf : CPolynomialAt 𝕜 f x) (hg : CPolynomialAt 𝕜 g x) : 
CPolynomialAt 𝕜 (f - g) x
参数：hf : CPolynomialAt 𝕜 f x；hg : CPolynomialAt 𝕜 g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `CPolynomialAt.add`：CPolynomialAt.add (hf : CPolynomialAt 𝕜 f x) (hg : CP
olynomialAt 𝕜 g x) : CPolynomialAt 𝕜 (f + g) x
· 使用定理 `CPolynomialAt.neg`：CPolynomialAt.neg (hf : CPolynomialAt 𝕜 f x) : CPolyn
omialAt 𝕜 (-f) x
-/
theorem CPolynomialAt.sub (hf : CPolynomialAt 𝕜 f x) (hg : CPolynomialAt 𝕜 g x) :
    CPolynomialAt 𝕜 (f - g) x := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg
/-
**CPolynomialOn.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CPolynomialOn.add {s : Set E} (hf : CPolynomialOn 𝕜 f s) (hg : CPolynomial
On 𝕜 g s) : CPolynomialOn 𝕜 (f + g) s
参数：hf : CPolynomialOn 𝕜 f s；hg : CPolynomialOn 𝕜 g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CPolynomialAt.add`：CPolynomialAt.add (hf : CPolynomialAt 𝕜 f x) (hg : CP
olynomialAt 𝕜 g x) : CPolynomialAt 𝕜 (f + g) x
-/
theorem CPolynomialOn.add {s : Set E} (hf : CPolynomialOn 𝕜 f s) (hg : CPolynomialOn 𝕜 g s) :
    CPolynomialOn 𝕜 (f + g) s :=
  fun z hz => (hf z hz).add (hg z hz)
/-
**CPolynomialOn.sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CPolynomialOn.sub {s : Set E} (hf : CPolynomialOn 𝕜 f s) (hg : CPolynomial
On 𝕜 g s) : CPolynomialOn 𝕜 (f - g) s
参数：hf : CPolynomialOn 𝕜 f s；hg : CPolynomialOn 𝕜 g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CPolynomialAt.sub`：CPolynomialAt.sub (hf : CPolynomialAt 𝕜 f x) (hg : CP
olynomialAt 𝕜 g x) : CPolynomialAt 𝕜 (f - g) x
-/
theorem CPolynomialOn.sub {s : Set E} (hf : CPolynomialOn 𝕜 f s) (hg : CPolynomialOn 𝕜 g s) :
    CPolynomialOn 𝕜 (f - g) s :=
  fun z hz => (hf z hz).sub (hg z hz)


/-!
### Continuous multilinear maps

We show that continuous multilinear maps are continuously polynomial, and therefore analytic.
-/

namespace ContinuousMultilinearMap

variable {ι : Type*} {Em : ι → Type*} [∀ i, NormedAddCommGroup (Em i)] [∀ i, NormedSpace 𝕜 (Em i)]
  [Fintype ι] (f : ContinuousMultilinearMap 𝕜 Em F) {x : Π i, Em i} {s : Set (Π i, Em i)}

open FormalMultilinearSeries

/-
**ContinuousMultilinearMap.hasFiniteFPowerSeriesOnBall** 是 Mathlib 中的一个定理，位于命名空间
 `ContinuousMultilinearMap`。
形式化陈述：∀ {𝕜 : Type u_1} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1
 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {ι : Type u_5} {Em : ι → T
ype u_6} [inst_3 : (i : ι) → NormedAddCommGroup (Em i)]   [inst_4 : (i : ι) → No
rmedSpace 𝕜 (Em i)] [inst_5 : Fintype ι] (f : ContinuousMultilinearMap 𝕜 Em F), 
  HasFiniteFPowerSeriesOnBall (⇑f) f.toFormalMultilinearSeries 0 (Fintype.card ι
 + 1) ⊤
参数：i : ι；Em i；i : ι；Em i；f : ContinuousMultilinearMap 𝕜 Em F；⇑f；Fintype.card ι +
 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFiniteFPowerSeriesOnBall.mk'`：HasFiniteFPowerSeriesOnBall.mk' {f : E 
-> F} {p : FormalMultilinearSeries 𝕜 E F} {x : E} {n : Nat} {r : Real>=0∞} (fini
te : forall (m : Nat)…
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
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.succ_le_iff`：∀ {m n : ℕ}, m.succ ≤ n ↔ m < n
· 使用定理 `ENNReal.zero_lt_top`：0 < ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_eq_single_of_mem`：∀ {ι : Type u_1} {M : Type u_4} [inst : Add
CommMonoid M] {s : Finset ι} {f : ι → M},   ∀ a ∈ s, (∀ b ∈ s, b ≠ a → f b = 0) 
→ ∑ x ∈ s, f x = …
· 使用定理 `Finset.self_mem_range_succ`：self_mem_range_succ (n : Nat) : n in range (
n + 1)
· 使用定理 `ContinuousMultilinearMap.toFormalMultilinearSeries.eq_1`：∀ {𝕜 : Type u} 
{F : Type w} [inst : Semiring 𝕜] [inst_1 : AddCommMonoid F] [inst_2 : _root_.Mod
ule 𝕜 F]   [inst_3 : TopologicalSpace F] [ins…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
protected theorem hasFiniteFPowerSeriesOnBall :
    HasFiniteFPowerSeriesOnBall f f.toFormalMultilinearSeries 0 (Fintype.card ι + 1) ⊤ :=
  .mk' (fun _ hm ↦ dif_neg (Nat.succ_le_iff.mp hm).ne) ENNReal.zero_lt_top fun y _ ↦ by
    rw [Finset.sum_eq_single_of_mem _ (Finset.self_mem_range_succ _), zero_add]
    · rw [toFormalMultilinearSeries, dif_pos rfl]; rfl
    · intro m _ ne; rw [toFormalMultilinearSeries, dif_neg ne.symm]; rfl
/-
**ContinuousMultilinearMap.cpolynomialAt** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMu
ltilinearMap`。
形式化陈述：cpolynomialAt : CPolynomialAt 𝕜 f x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFiniteFPowerSeriesOnBall.cpolynomialAt_of_mem`：HasFiniteFPowerSeriesO
nBall.cpolynomialAt_of_mem (hf : HasFiniteFPowerSeriesOnBall f p x n r) (h : y i
n Metric.eball x r) : CPolynomialAt 𝕜 …
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
· 使用定理 `ContinuousMultilinearMap.hasFiniteFPowerSeriesOnBall`：∀ {𝕜 : Type u_1} {
F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup F]
   [inst_2 : NormedSpace 𝕜 F] {ι : Type u_…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.eball_top`：Metric.eball_top (x : α) : eball x ⊤ = univ
-/
lemma cpolynomialAt : CPolynomialAt 𝕜 f x :=
  f.hasFiniteFPowerSeriesOnBall.cpolynomialAt_of_mem
    (by simp only [Metric.eball_top, Set.mem_univ])
/-
**ContinuousMultilinearMap.cpolynomialOn** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMu
ltilinearMap`。
形式化陈述：cpolynomialOn : CPolynomialOn 𝕜 f s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousMultilinearMap.cpolynomialAt`：cpolynomialAt : CPolynomialAt 𝕜 
f x
-/
lemma cpolynomialOn : CPolynomialOn 𝕜 f s := fun _ _ ↦ f.cpolynomialAt
/-
**ContinuousMultilinearMap.analyticOnNhd** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMu
ltilinearMap`。
形式化陈述：analyticOnNhd : AnalyticOnNhd 𝕜 f s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CPolynomialOn.analyticOnNhd`：CPolynomialOn.analyticOnNhd {s : Set E} (hf
 : CPolynomialOn 𝕜 f s) : AnalyticOnNhd 𝕜 f s
· 使用引理 `ContinuousMultilinearMap.cpolynomialOn`：cpolynomialOn : CPolynomialOn 𝕜 
f s
-/
lemma analyticOnNhd : AnalyticOnNhd 𝕜 f s := f.cpolynomialOn.analyticOnNhd
/-
**ContinuousMultilinearMap.analyticOn** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMulti
linearMap`。
形式化陈述：analyticOn : AnalyticOn 𝕜 f s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticOnNhd.analyticOn`：AnalyticOnNhd.analyticOn (hf : AnalyticOnNhd 𝕜
 f s) : AnalyticOn 𝕜 f s
· 使用引理 `ContinuousMultilinearMap.analyticOnNhd`：analyticOnNhd : AnalyticOnNhd 𝕜 
f s
-/
lemma analyticOn : AnalyticOn 𝕜 f s := f.analyticOnNhd.analyticOn
/-
**ContinuousMultilinearMap.analyticAt** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMulti
linearMap`。
形式化陈述：analyticAt : AnalyticAt 𝕜 f x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CPolynomialAt.analyticAt`：CPolynomialAt.analyticAt (hf : CPolynomialAt 𝕜
 f x) : AnalyticAt 𝕜 f x
· 使用引理 `ContinuousMultilinearMap.cpolynomialAt`：cpolynomialAt : CPolynomialAt 𝕜 
f x
-/
lemma analyticAt : AnalyticAt 𝕜 f x := f.cpolynomialAt.analyticAt
/-
**ContinuousMultilinearMap.analyticWithinAt** 是 Mathlib 中的一个引理，位于命名空间 `Continuou
sMultilinearMap`。
形式化陈述：analyticWithinAt : AnalyticWithinAt 𝕜 f s x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticAt.analyticWithinAt`：AnalyticAt.analyticWithinAt (hf : AnalyticA
t 𝕜 f x) : AnalyticWithinAt 𝕜 f s x
· 使用引理 `ContinuousMultilinearMap.analyticAt`：analyticAt : AnalyticAt 𝕜 f x
-/
lemma analyticWithinAt : AnalyticWithinAt 𝕜 f s x := f.analyticAt.analyticWithinAt

end ContinuousMultilinearMap


/-!
### Continuous linear maps into continuous multilinear maps

We show that a continuous linear map into continuous multilinear maps is continuously polynomial
(as a function of two variables, i.e., uncurried). Therefore, it is also analytic.
-/

namespace ContinuousLinearMap

variable {ι : Type*} {Em : ι → Type*} [∀ i, NormedAddCommGroup (Em i)] [∀ i, NormedSpace 𝕜 (Em i)]
  [Fintype ι] (f : G →L[𝕜] ContinuousMultilinearMap 𝕜 Em F)
  {s : Set (G × (Π i, Em i))} {x : G × (Π i, Em i)}

/-- Formal multilinear series associated to a linear map into multilinear maps. -/
/-
**ContinuousLinearMap.toFormalMultilinearSeriesOfMultilinear** 是 Mathlib 中的一个定义，
位于命名空间 `ContinuousLinearMap`。
形式化陈述：toFormalMultilinearSeriesOfMultilinear : FormalMultilinearSeries 𝕜 (G × (Π
 i, Em i)) F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Formal multilinear series associated to a linear map into multilinear maps.
-/
noncomputable def toFormalMultilinearSeriesOfMultilinear :
    FormalMultilinearSeries 𝕜 (G × (Π i, Em i)) F :=
  fun n ↦ if h : Fintype.card (Option ι) = n then
    (f.continuousMultilinearMapOption).domDomCongr (Fintype.equivFinOfCardEq h)
  else 0
/-
**ContinuousLinearMap.hasFiniteFPowerSeriesOnBall_uncurry_of_multilinear** 是 Mat
hlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：∀ {𝕜 : Type u_1} {F : Type u_3} {G : Type u_4} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] [inst_3 : N
ormedAddCommGroup G] [inst_4 : NormedSpace 𝕜 G] {ι : Type u_5}   {Em : ι → Type 
u_6} [inst_5 : (i : ι) → NormedAddCommGroup (Em i)] [inst_6 : (i : ι) → NormedSp
ace 𝕜 (Em i)]   [inst_7 : Fintype ι] (f : G →L[𝕜] ContinuousMultilinearMap 𝕜 Em 
F),   HasFiniteFPowerSeriesOnBall (fun p => (f p.1) p.2) f.toFormalMultilinearSe
riesOfMultilinear 0     (Fintype.card (Option ι) + 1) ⊤
参数：i : ι；Em i；i : ι；Em i；f : G →L[𝕜] ContinuousMultilinearMap 𝕜 Em F；fun p => (f
 p.1) p.2；Fintype.card (Option ι) + 1。
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
· 使用定理 `HasFiniteFPowerSeriesOnBall.mk'`：HasFiniteFPowerSeriesOnBall.mk' {f : E 
-> F} {p : FormalMultilinearSeries 𝕜 E F} {x : E} {n : Nat} {r : Real>=0∞} (fini
te : forall (m : Nat)…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Nat.ne_of_lt`：∀ {a b : ℕ}, a < b → a ≠ b
· 使用定理 `ENNReal.zero_lt_top`：0 < ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_eq_single_of_mem`：∀ {ι : Type u_1} {M : Type u_4} [inst : Add
CommMonoid M] {s : Finset ι} {f : ι → M},   ∀ a ∈ s, (∀ b ∈ s, b ≠ a → f b = 0) 
→ ∑ x ∈ s, f x = …
· 使用定理 `Finset.self_mem_range_succ`：self_mem_range_succ (n : Nat) : n in range (
n + 1)
· 使用定理 `ContinuousLinearMap.toFormalMultilinearSeriesOfMultilinear.eq_1`：∀ {𝕜 : 
Type u_1} {F : Type u_3} {G : Type u_4} [inst : NontriviallyNormedField 𝕜] [inst
_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 …
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
protected theorem hasFiniteFPowerSeriesOnBall_uncurry_of_multilinear :
    HasFiniteFPowerSeriesOnBall (fun (p : G × (Π i, Em i)) ↦ f p.1 p.2)
      f.toFormalMultilinearSeriesOfMultilinear 0 (Fintype.card (Option ι) + 1) ⊤ := by
  apply HasFiniteFPowerSeriesOnBall.mk' ?_ ENNReal.zero_lt_top ?_
  · intro m hm
    apply dif_neg
    exact Nat.ne_of_lt hm
  · intro y _
    rw [Finset.sum_eq_single_of_mem _ (Finset.self_mem_range_succ _), zero_add]
    · rw [toFormalMultilinearSeriesOfMultilinear, dif_pos rfl]; rfl
    · intro m _ ne; rw [toFormalMultilinearSeriesOfMultilinear, dif_neg ne.symm]; rfl
/-
**ContinuousLinearMap.cpolynomialAt_uncurry_of_multilinear** 是 Mathlib 中的一个引理，位于
命名空间 `ContinuousLinearMap`。
形式化陈述：cpolynomialAt_uncurry_of_multilinear : CPolynomialAt 𝕜 (fun (p : G × (Π i,
 Em i)) => f p.1 p.2) x
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
· 使用定理 `HasFiniteFPowerSeriesOnBall.cpolynomialAt_of_mem`：HasFiniteFPowerSeriesO
nBall.cpolynomialAt_of_mem (hf : HasFiniteFPowerSeriesOnBall f p x n r) (h : y i
n Metric.eball x r) : CPolynomialAt 𝕜 …
· 使用定理 `ContinuousLinearMap.hasFiniteFPowerSeriesOnBall_uncurry_of_multilinear`：
∀ {𝕜 : Type u_1} {F : Type u_3} {G : Type u_4} [inst : NontriviallyNormedField 𝕜
] [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.eball_top`：Metric.eball_top (x : α) : eball x ⊤ = univ
-/
lemma cpolynomialAt_uncurry_of_multilinear :
    CPolynomialAt 𝕜 (fun (p : G × (Π i, Em i)) ↦ f p.1 p.2) x :=
  f.hasFiniteFPowerSeriesOnBall_uncurry_of_multilinear.cpolynomialAt_of_mem
    (by simp only [Metric.eball_top, Set.mem_univ])
/-
**ContinuousLinearMap.cpolynomialOn_uncurry_of_multilinear** 是 Mathlib 中的一个引理，位于
命名空间 `ContinuousLinearMap`。
形式化陈述：cpolynomialOn_uncurry_of_multilinear : CPolynomialOn 𝕜 (fun (p : G × (Π i,
 Em i)) => f p.1 p.2) s
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
· 使用引理 `ContinuousLinearMap.cpolynomialAt_uncurry_of_multilinear`：cpolynomialAt_
uncurry_of_multilinear : CPolynomialAt 𝕜 (fun (p : G × (Π i, Em i)) => f p.1 p.2
) x
-/
lemma cpolynomialOn_uncurry_of_multilinear :
    CPolynomialOn 𝕜 (fun (p : G × (Π i, Em i)) ↦ f p.1 p.2) s :=
  fun _ _ ↦ f.cpolynomialAt_uncurry_of_multilinear
/-
**ContinuousLinearMap.analyticOnNhd_uncurry_of_multilinear** 是 Mathlib 中的一个引理，位于
命名空间 `ContinuousLinearMap`。
形式化陈述：analyticOnNhd_uncurry_of_multilinear : AnalyticOnNhd 𝕜 (fun (p : G × (Π i,
 Em i)) => f p.1 p.2) s
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
· 使用定理 `CPolynomialOn.analyticOnNhd`：CPolynomialOn.analyticOnNhd {s : Set E} (hf
 : CPolynomialOn 𝕜 f s) : AnalyticOnNhd 𝕜 f s
· 使用引理 `ContinuousLinearMap.cpolynomialOn_uncurry_of_multilinear`：cpolynomialOn_
uncurry_of_multilinear : CPolynomialOn 𝕜 (fun (p : G × (Π i, Em i)) => f p.1 p.2
) s
-/
lemma analyticOnNhd_uncurry_of_multilinear :
    AnalyticOnNhd 𝕜 (fun (p : G × (Π i, Em i)) ↦ f p.1 p.2) s :=
  f.cpolynomialOn_uncurry_of_multilinear.analyticOnNhd
/-
**ContinuousLinearMap.analyticOn_uncurry_of_multilinear** 是 Mathlib 中的一个引理，位于命名空
间 `ContinuousLinearMap`。
形式化陈述：analyticOn_uncurry_of_multilinear : AnalyticOn 𝕜 (fun (p : G × (Π i, Em i)
) => f p.1 p.2) s
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
· 使用引理 `AnalyticOnNhd.analyticOn`：AnalyticOnNhd.analyticOn (hf : AnalyticOnNhd 𝕜
 f s) : AnalyticOn 𝕜 f s
· 使用引理 `ContinuousLinearMap.analyticOnNhd_uncurry_of_multilinear`：analyticOnNhd_
uncurry_of_multilinear : AnalyticOnNhd 𝕜 (fun (p : G × (Π i, Em i)) => f p.1 p.2
) s
-/
lemma analyticOn_uncurry_of_multilinear :
    AnalyticOn 𝕜 (fun (p : G × (Π i, Em i)) ↦ f p.1 p.2) s :=
  f.analyticOnNhd_uncurry_of_multilinear.analyticOn
/-
**ContinuousLinearMap.analyticAt_uncurry_of_multilinear** 是 Mathlib 中的一个引理，位于命名空
间 `ContinuousLinearMap`。
形式化陈述：analyticAt_uncurry_of_multilinear : AnalyticAt 𝕜 (fun (p : G × (Π i, Em i)
) => f p.1 p.2) x
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
· 使用定理 `CPolynomialAt.analyticAt`：CPolynomialAt.analyticAt (hf : CPolynomialAt 𝕜
 f x) : AnalyticAt 𝕜 f x
· 使用引理 `ContinuousLinearMap.cpolynomialAt_uncurry_of_multilinear`：cpolynomialAt_
uncurry_of_multilinear : CPolynomialAt 𝕜 (fun (p : G × (Π i, Em i)) => f p.1 p.2
) x
-/
lemma analyticAt_uncurry_of_multilinear : AnalyticAt 𝕜 (fun (p : G × (Π i, Em i)) ↦ f p.1 p.2) x :=
  f.cpolynomialAt_uncurry_of_multilinear.analyticAt
/-
**ContinuousLinearMap.analyticWithinAt_uncurry_of_multilinear** 是 Mathlib 中的一个引理
，位于命名空间 `ContinuousLinearMap`。
形式化陈述：analyticWithinAt_uncurry_of_multilinear : AnalyticWithinAt 𝕜 (fun (p : G ×
 (Π i, Em i)) => f p.1 p.2) s x
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
· 使用引理 `AnalyticAt.analyticWithinAt`：AnalyticAt.analyticWithinAt (hf : AnalyticA
t 𝕜 f x) : AnalyticWithinAt 𝕜 f s x
· 使用引理 `ContinuousLinearMap.analyticAt_uncurry_of_multilinear`：analyticAt_uncurr
y_of_multilinear : AnalyticAt 𝕜 (fun (p : G × (Π i, Em i)) => f p.1 p.2) x
-/
lemma analyticWithinAt_uncurry_of_multilinear :
    AnalyticWithinAt 𝕜 (fun (p : G × (Π i, Em i)) ↦ f p.1 p.2) s x :=
  f.analyticAt_uncurry_of_multilinear.analyticWithinAt

end ContinuousLinearMap

namespace ContinuousMultilinearMap

variable {ι : Type*} {Em Fm : ι → Type*}
  [∀ i, NormedAddCommGroup (Em i)] [∀ i, NormedSpace 𝕜 (Em i)]
  [∀ i, NormedAddCommGroup (Fm i)] [∀ i, NormedSpace 𝕜 (Fm i)]
  [Fintype ι] (f : ContinuousMultilinearMap 𝕜 Em (G →L[𝕜] F))
  {s : Set ((Π i, Em i) × G)} {x : (Π i, Em i) × G}

/-
**ContinuousMultilinearMap.cpolynomialAt_uncurry_of_linear** 是 Mathlib 中的一个引理，位于
命名空间 `ContinuousMultilinearMap`。
形式化陈述：cpolynomialAt_uncurry_of_linear : CPolynomialAt 𝕜 (fun (p : (Π i, Em i) × 
G) => f p.1 p.2) x
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
· 使用定理 `ContinuousLinearMap.cpolynomialAt`：∀ {𝕜 : Type u_1} [inst : Nontrivially
NormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 E] {F : Type u_…
· 使用定理 `CPolynomialAt.comp`：CPolynomialAt.comp {g : F -> G} {f : E -> F} {x : E}
 (hg : CPolynomialAt 𝕜 g (f x)) (hf : CPolynomialAt 𝕜 f x) : CPolynomialAt 𝕜 (g 
∘ f) x
· 使用引理 `ContinuousLinearMap.cpolynomialAt_uncurry_of_multilinear`：cpolynomialAt_
uncurry_of_multilinear : CPolynomialAt 𝕜 (fun (p : G × (Π i, Em i)) => f p.1 p.2
) x
-/
lemma cpolynomialAt_uncurry_of_linear :
    CPolynomialAt 𝕜 (fun (p : (Π i, Em i) × G) ↦ f p.1 p.2) x := by
  have : CPolynomialAt 𝕜 (ContinuousLinearEquiv.prodComm 𝕜 (Π i, Em i) G).toContinuousLinearMap x :=
    ContinuousLinearMap.cpolynomialAt _ _
  exact f.flipLinear.cpolynomialAt_uncurry_of_multilinear.comp this
/-
**ContinuousMultilinearMap.cpolyomialOn_uncurry_of_linear** 是 Mathlib 中的一个引理，位于命
名空间 `ContinuousMultilinearMap`。
形式化陈述：cpolyomialOn_uncurry_of_linear : CPolynomialOn 𝕜 (fun (p : (Π i, Em i) × G
) => f p.1 p.2) s
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
· 使用引理 `ContinuousMultilinearMap.cpolynomialAt_uncurry_of_linear`：cpolynomialAt_
uncurry_of_linear : CPolynomialAt 𝕜 (fun (p : (Π i, Em i) × G) => f p.1 p.2) x
-/
lemma cpolyomialOn_uncurry_of_linear :
    CPolynomialOn 𝕜 (fun (p : (Π i, Em i) × G) ↦ f p.1 p.2) s :=
  fun _ _ ↦ f.cpolynomialAt_uncurry_of_linear
/-
**ContinuousMultilinearMap.analyticOnNhd_uncurry_of_linear** 是 Mathlib 中的一个引理，位于
命名空间 `ContinuousMultilinearMap`。
形式化陈述：analyticOnNhd_uncurry_of_linear : AnalyticOnNhd 𝕜 (fun (p : (Π i, Em i) × 
G) => f p.1 p.2) s
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
· 使用定理 `CPolynomialOn.analyticOnNhd`：CPolynomialOn.analyticOnNhd {s : Set E} (hf
 : CPolynomialOn 𝕜 f s) : AnalyticOnNhd 𝕜 f s
· 使用引理 `ContinuousMultilinearMap.cpolyomialOn_uncurry_of_linear`：cpolyomialOn_un
curry_of_linear : CPolynomialOn 𝕜 (fun (p : (Π i, Em i) × G) => f p.1 p.2) s
-/
lemma analyticOnNhd_uncurry_of_linear :
    AnalyticOnNhd 𝕜 (fun (p : (Π i, Em i) × G) ↦ f p.1 p.2) s :=
  f.cpolyomialOn_uncurry_of_linear.analyticOnNhd
/-
**ContinuousMultilinearMap.analyticOn_uncurry_of_linear** 是 Mathlib 中的一个引理，位于命名空
间 `ContinuousMultilinearMap`。
形式化陈述：analyticOn_uncurry_of_linear : AnalyticOn 𝕜 (fun (p : (Π i, Em i) × G) => 
f p.1 p.2) s
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
· 使用引理 `AnalyticOnNhd.analyticOn`：AnalyticOnNhd.analyticOn (hf : AnalyticOnNhd 𝕜
 f s) : AnalyticOn 𝕜 f s
· 使用引理 `ContinuousMultilinearMap.analyticOnNhd_uncurry_of_linear`：analyticOnNhd_
uncurry_of_linear : AnalyticOnNhd 𝕜 (fun (p : (Π i, Em i) × G) => f p.1 p.2) s
-/
lemma analyticOn_uncurry_of_linear :
    AnalyticOn 𝕜 (fun (p : (Π i, Em i) × G) ↦ f p.1 p.2) s :=
  f.analyticOnNhd_uncurry_of_linear.analyticOn
/-
**ContinuousMultilinearMap.analyticAt_uncurry_of_linear** 是 Mathlib 中的一个引理，位于命名空
间 `ContinuousMultilinearMap`。
形式化陈述：analyticAt_uncurry_of_linear : AnalyticAt 𝕜 (fun (p : (Π i, Em i) × G) => 
f p.1 p.2) x
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
· 使用定理 `CPolynomialAt.analyticAt`：CPolynomialAt.analyticAt (hf : CPolynomialAt 𝕜
 f x) : AnalyticAt 𝕜 f x
· 使用引理 `ContinuousMultilinearMap.cpolynomialAt_uncurry_of_linear`：cpolynomialAt_
uncurry_of_linear : CPolynomialAt 𝕜 (fun (p : (Π i, Em i) × G) => f p.1 p.2) x
-/
lemma analyticAt_uncurry_of_linear : AnalyticAt 𝕜 (fun (p : (Π i, Em i) × G) ↦ f p.1 p.2) x :=
  f.cpolynomialAt_uncurry_of_linear.analyticAt
/-
**ContinuousMultilinearMap.analyticWithinAt_uncurry_of_linear** 是 Mathlib 中的一个引理
，位于命名空间 `ContinuousMultilinearMap`。
形式化陈述：analyticWithinAt_uncurry_of_linear : AnalyticWithinAt 𝕜 (fun (p : (Π i, Em
 i) × G) => f p.1 p.2) s x
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
· 使用引理 `AnalyticAt.analyticWithinAt`：AnalyticAt.analyticWithinAt (hf : AnalyticA
t 𝕜 f x) : AnalyticWithinAt 𝕜 f s x
· 使用引理 `ContinuousMultilinearMap.analyticAt_uncurry_of_linear`：analyticAt_uncurr
y_of_linear : AnalyticAt 𝕜 (fun (p : (Π i, Em i) × G) => f p.1 p.2) x
-/
lemma analyticWithinAt_uncurry_of_linear :
    AnalyticWithinAt 𝕜 (fun (p : (Π i, Em i) × G) ↦ f p.1 p.2) s x :=
  f.analyticAt_uncurry_of_linear.analyticWithinAt

variable {t : Set ((Π i, Fm i →L[𝕜] Em i) × (ContinuousMultilinearMap 𝕜 Em G))}
  {q : (Π i, Fm i →L[𝕜] Em i) × (ContinuousMultilinearMap 𝕜 Em G)}
/-
**ContinuousMultilinearMap.cpolynomialAt_uncurry_compContinuousLinearMap** 是 Mat
hlib 中的一个引理，位于命名空间 `ContinuousMultilinearMap`。
形式化陈述：cpolynomialAt_uncurry_compContinuousLinearMap : CPolynomialAt 𝕜 (fun (p : 
(Π i, Fm i ->L[𝕜] Em i) × (ContinuousMultilinearMap 𝕜 Em G)) => p.2.compContinuo
usLinearMap p.1) q
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousMultilinearMap.cpolynomialAt_uncurry_of_linear`：cpolynomialAt_
uncurry_of_linear : CPolynomialAt 𝕜 (fun (p : (Π i, Em i) × G) => f p.1 p.2) x
-/
lemma cpolynomialAt_uncurry_compContinuousLinearMap :
    CPolynomialAt 𝕜 (fun (p : (Π i, Fm i →L[𝕜] Em i) × (ContinuousMultilinearMap 𝕜 Em G))
      ↦ p.2.compContinuousLinearMap p.1) q :=
  cpolynomialAt_uncurry_of_linear
    (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear 𝕜 Fm Em G)
/-
**ContinuousMultilinearMap.cpolynomialOn_uncurry_compContinuousLinearMap** 是 Mat
hlib 中的一个引理，位于命名空间 `ContinuousMultilinearMap`。
形式化陈述：cpolynomialOn_uncurry_compContinuousLinearMap : CPolynomialOn 𝕜 (fun (p : 
(Π i, Fm i ->L[𝕜] Em i) × (ContinuousMultilinearMap 𝕜 Em G)) => p.2.compContinuo
usLinearMap p.1) t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousMultilinearMap.cpolyomialOn_uncurry_of_linear`：cpolyomialOn_un
curry_of_linear : CPolynomialOn 𝕜 (fun (p : (Π i, Em i) × G) => f p.1 p.2) s
-/
lemma cpolynomialOn_uncurry_compContinuousLinearMap :
    CPolynomialOn 𝕜 (fun (p : (Π i, Fm i →L[𝕜] Em i) × (ContinuousMultilinearMap 𝕜 Em G))
      ↦ p.2.compContinuousLinearMap p.1) t :=
  cpolyomialOn_uncurry_of_linear
    (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear 𝕜 Fm Em G)
/-
**ContinuousMultilinearMap.analyticOnNhd_uncurry_compContinuousLinearMap** 是 Mat
hlib 中的一个引理，位于命名空间 `ContinuousMultilinearMap`。
形式化陈述：analyticOnNhd_uncurry_compContinuousLinearMap : AnalyticOnNhd 𝕜 (fun (p : 
(Π i, Fm i ->L[𝕜] Em i) × (ContinuousMultilinearMap 𝕜 Em G)) => p.2.compContinuo
usLinearMap p.1) t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousMultilinearMap.analyticOnNhd_uncurry_of_linear`：analyticOnNhd_
uncurry_of_linear : AnalyticOnNhd 𝕜 (fun (p : (Π i, Em i) × G) => f p.1 p.2) s
-/
lemma analyticOnNhd_uncurry_compContinuousLinearMap :
    AnalyticOnNhd 𝕜 (fun (p : (Π i, Fm i →L[𝕜] Em i) × (ContinuousMultilinearMap 𝕜 Em G))
      ↦ p.2.compContinuousLinearMap p.1) t :=
  analyticOnNhd_uncurry_of_linear
    (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear 𝕜 Fm Em G)
/-
**ContinuousMultilinearMap.analyticOn_uncurry_compContinuousLinearMap** 是 Mathli
b 中的一个引理，位于命名空间 `ContinuousMultilinearMap`。
形式化陈述：analyticOn_uncurry_compContinuousLinearMap : AnalyticOn 𝕜 (fun (p : (Π i, 
Fm i ->L[𝕜] Em i) × (ContinuousMultilinearMap 𝕜 Em G)) => p.2.compContinuousLine
arMap p.1) t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousMultilinearMap.analyticOn_uncurry_of_linear`：analyticOn_uncurr
y_of_linear : AnalyticOn 𝕜 (fun (p : (Π i, Em i) × G) => f p.1 p.2) s
-/
lemma analyticOn_uncurry_compContinuousLinearMap :
    AnalyticOn 𝕜 (fun (p : (Π i, Fm i →L[𝕜] Em i) × (ContinuousMultilinearMap 𝕜 Em G))
      ↦ p.2.compContinuousLinearMap p.1) t :=
  analyticOn_uncurry_of_linear
    (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear 𝕜 Fm Em G)
/-
**ContinuousMultilinearMap.analyticAt_uncurry_compContinuousLinearMap** 是 Mathli
b 中的一个引理，位于命名空间 `ContinuousMultilinearMap`。
形式化陈述：analyticAt_uncurry_compContinuousLinearMap : AnalyticAt 𝕜 (fun (p : (Π i, 
Fm i ->L[𝕜] Em i) × (ContinuousMultilinearMap 𝕜 Em G)) => p.2.compContinuousLine
arMap p.1) q
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousMultilinearMap.analyticAt_uncurry_of_linear`：analyticAt_uncurr
y_of_linear : AnalyticAt 𝕜 (fun (p : (Π i, Em i) × G) => f p.1 p.2) x
-/
lemma analyticAt_uncurry_compContinuousLinearMap :
    AnalyticAt 𝕜 (fun (p : (Π i, Fm i →L[𝕜] Em i) × (ContinuousMultilinearMap 𝕜 Em G))
      ↦ p.2.compContinuousLinearMap p.1) q :=
  analyticAt_uncurry_of_linear
    (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear 𝕜 Fm Em G)
/-
**ContinuousMultilinearMap.analyticWithinAt_uncurry_compContinuousLinearMap** 是 
Mathlib 中的一个引理，位于命名空间 `ContinuousMultilinearMap`。
形式化陈述：analyticWithinAt_uncurry_compContinuousLinearMap : AnalyticWithinAt 𝕜 (fun
 (p : (Π i, Fm i ->L[𝕜] Em i) × (ContinuousMultilinearMap 𝕜 Em G)) => p.2.compCo
ntinuousLinearMap p.1) t q
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousMultilinearMap.analyticWithinAt_uncurry_of_linear`：analyticWit
hinAt_uncurry_of_linear : AnalyticWithinAt 𝕜 (fun (p : (Π i, Em i) × G) => f p.1
 p.2) s x
-/
lemma analyticWithinAt_uncurry_compContinuousLinearMap :
    AnalyticWithinAt 𝕜 (fun (p : (Π i, Fm i →L[𝕜] Em i) × (ContinuousMultilinearMap 𝕜 Em G))
      ↦ p.2.compContinuousLinearMap p.1) t q :=
  analyticWithinAt_uncurry_of_linear
    (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear 𝕜 Fm Em G)

end ContinuousMultilinearMap

