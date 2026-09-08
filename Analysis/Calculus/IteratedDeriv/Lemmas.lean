/-
Copyright (c) 2023 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Ruben Van de Velde
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# One-dimensional iterated derivatives

This file contains a number of further results on `iteratedDerivWithin` that need more imports
than are available in `Mathlib/Analysis/Calculus/IteratedDeriv/Defs.lean`.
-/

public section

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : ℕ} {x : 𝕜} {s : Set 𝕜} (hx : x ∈ s) (h : UniqueDiffOn 𝕜 s) {f g : 𝕜 → F}
  -- For maximum generality, results about `smul` involve a second type besides `𝕜`,
  -- with varying hypotheses.
  -- * `R`: general type.
  {R : Type*} [DistribSMul R F] [SMulCommClass 𝕜 R F] [ContinuousConstSMul R F]
  -- * `𝕝`: division semiring. (Addition in `𝕝` is not used, so the results would work with a
  -- `GroupWithZero` if we had a `DistribSMulWithZero` typeclass.)
  {𝕝 : Type*} [DivisionSemiring 𝕝] [Module 𝕝 F] [SMulCommClass 𝕜 𝕝 F] [ContinuousConstSMul 𝕝 F]
  -- * `𝔸`: normed `𝕜`-algebra.
  {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕜 𝔸] [Module 𝔸 F] [IsBoundedSMul 𝔸 F]
    [IsScalarTower 𝕜 𝔸 F]
  -- * `𝕜'`: normed `𝕜`-division algebra.
  {𝕜' : Type*} [NormedDivisionRing 𝕜'] [NormedAlgebra 𝕜 𝕜']
    [Module 𝕜' F] [SMulCommClass 𝕜 𝕜' F] [ContinuousSMul 𝕜' F]

section one_dimensional

open scoped Topology

section

/-
**Filter.EventuallyEq.iteratedDerivWithin_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.iteratedDerivWithin_eq (hfg : f =ᶠ[𝓝[s] x] g) (hfg' : 
f x = g x) : iteratedDerivWithin n f s x = iteratedDerivWithin n g s x
参数：hfg : f =ᶠ[𝓝[s] x] g；hfg' : f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.EventuallyEq.iteratedFDerivWithin_eq`：Filter.EventuallyEq.iterate
dFDerivWithin_eq (h : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) (n : Nat) : iteratedFDe
rivWithin 𝕜 n f₁ s x = iteratedFD…
-/
theorem Filter.EventuallyEq.iteratedDerivWithin_eq (hfg : f =ᶠ[𝓝[s] x] g) (hfg' : f x = g x) :
    iteratedDerivWithin n f s x = iteratedDerivWithin n g s x :=
  congr($(hfg.iteratedFDerivWithin_eq hfg' n) _)
/-
**Filter.EventuallyEq.iteratedDerivWithin'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.iteratedDerivWithin' {s t : Set 𝕜} (h : f =ᶠ[𝓝[s] x] g
) (ht : t subseteq s) (n : Nat) : iteratedDerivWithin n f t =ᶠ[𝓝[s] x] iteratedD
erivWithin n g t
参数：h : f =ᶠ[𝓝[s] x] g；ht : t subseteq s；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.fun_comp`：∀ {α : Type u} {β : Type v} {γ : Type w} {
f g : α → β} {l : Filter α}, f =ᶠ[l] g → ∀ (h : β → γ), h ∘ f =ᶠ[l] h ∘ g
· 使用定理 `Filter.EventuallyEq.iteratedFDerivWithin'`：Filter.EventuallyEq.iteratedF
DerivWithin' (h : f₁ =ᶠ[𝓝[s] x] f) (ht : t subseteq s) (n : Nat) : iteratedFDeri
vWithin 𝕜 n f₁ t =ᶠ[𝓝[s] x] ite…
-/
theorem Filter.EventuallyEq.iteratedDerivWithin' {s t : Set 𝕜}
    (h : f =ᶠ[𝓝[s] x] g) (ht : t ⊆ s) (n : ℕ) :
    iteratedDerivWithin n f t =ᶠ[𝓝[s] x] iteratedDerivWithin n g t := by
  unfold iteratedDerivWithin
  exact h.iteratedFDerivWithin' ht n |>.fun_comp (fun a ↦ a fun _ ↦ 1)

/-- If two functions agree in a neighborhood within `s`, then so do their iterated derivatives. -/
/-
**Filter.EventuallyEq.iteratedDerivWithin** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Even
tuallyEq`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {F : Type u_2} [inst_1
 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {x : 𝕜} {f g : 𝕜 → F} {s :
 Set 𝕜},   f =ᶠ[nhdsWithin x s] g → ∀ (n : ℕ), iteratedDerivWithin n f s =ᶠ[nhds
Within x s] iteratedDerivWithin n g s
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.iteratedDerivWithin'`：Filter.EventuallyEq.iteratedDe
rivWithin' {s t : Set 𝕜} (h : f =ᶠ[𝓝[s] x] g) (ht : t subseteq s) (n : Nat) : it
eratedDerivWithin n f t =ᶠ[𝓝[s…
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s

--- 原说明 ---
If two functions agree in a neighborhood within `s`, then so do their iterated d
erivatives.
-/
protected lemma Filter.EventuallyEq.iteratedDerivWithin {s : Set 𝕜} (h : f =ᶠ[𝓝[s] x] g) (n : ℕ) :
    iteratedDerivWithin n f s =ᶠ[𝓝[s] x] iteratedDerivWithin n g s :=
  h.iteratedDerivWithin' Set.Subset.rfl n
/-
**Filter.EventuallyEq.iteratedDerivWithin_eq_of_nhds_insert** 是 Mathlib 中的一个定理，位
于命名空间 ``。
形式化陈述：Filter.EventuallyEq.iteratedDerivWithin_eq_of_nhds_insert {𝕜 F : Type*} [N
ontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F] (n : Nat) {f 
g : 𝕜 -> F} {x : 𝕜} {s : Set 𝕜} (hfg : f =ᶠ[𝓝[insert x s] x] g) : iteratedDerivW
ithin n f s x = iteratedDerivWithin n g s x
参数：n : Nat；hfg : f =ᶠ[𝓝[insert x s] x] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.iteratedDerivWithin_eq`：Filter.EventuallyEq.iterated
DerivWithin_eq (hfg : f =ᶠ[𝓝[s] x] g) (hfg' : f x = g x) : iteratedDerivWithin n
 f s x = iteratedDerivWithin n g…
· 使用定理 `Filter.EventuallyEq.filter_mono`：∀ {α : Type u} {β : Type v} {l l' : Fil
ter α} {f g : α → β}, f =ᶠ[l] g → l' ≤ l → f =ᶠ[l'] g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsWithin_insert`：nhdsWithin_insert (a : α) (s : Set α) : 𝓝[insert a s]
 a = pure a ⊔ 𝓝[s] a
· 使用定理 `Filter.EventuallyEq.eq_of_nhdsWithin`：Filter.EventuallyEq.eq_of_nhdsWith
in {s : Set α} {f g : α -> β} {a : α} (h : f =ᶠ[𝓝[s] a] g) (hmem : a in s) : f a
 = g a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
theorem Filter.EventuallyEq.iteratedDerivWithin_eq_of_nhds_insert
    {𝕜 F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] (n : ℕ) {f g : 𝕜 → F} {x : 𝕜} {s : Set 𝕜}
    (hfg : f =ᶠ[𝓝[insert x s] x] g) :
    iteratedDerivWithin n f s x = iteratedDerivWithin n g s x :=
  (hfg.filter_mono (by simp)).iteratedDerivWithin_eq (hfg.eq_of_nhdsWithin (by simp))
/-
**iteratedDerivWithin_congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDerivWithin_congr (hfg : Set.EqOn f g s) : Set.EqOn (iteratedDeriv
Within n f s) (iteratedDerivWithin n g s) s
参数：hfg : Set.EqOn f g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.iteratedDerivWithin_eq`：Filter.EventuallyEq.iterated
DerivWithin_eq (hfg : f =ᶠ[𝓝[s] x] g) (hfg' : f x = g x) : iteratedDerivWithin n
 f s x = iteratedDerivWithin n g…
· 使用定理 `Set.EqOn.eventuallyEq_nhdsWithin`：Set.EqOn.eventuallyEq_nhdsWithin {f g 
: α -> β} {s : Set α} {a : α} (h : EqOn f g s) : f =ᶠ[𝓝[s] a] g
-/
theorem iteratedDerivWithin_congr (hfg : Set.EqOn f g s) :
    Set.EqOn (iteratedDerivWithin n f s) (iteratedDerivWithin n g s) s :=
  fun _ hx ↦ hfg.eventuallyEq_nhdsWithin.iteratedDerivWithin_eq (hfg hx)

include h hx in
/-
**iteratedDerivWithin_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDerivWithin_add (hf : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWi
thinAt 𝕜 n g s x) : iteratedDerivWithin n (f + g) s x = iteratedDerivWithin n f 
s x + iteratedDerivWithin n g s x
参数：hf : ContDiffWithinAt 𝕜 n f s x；hg : ContDiffWithinAt 𝕜 n g s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iteratedFDerivWithin_add_apply`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {F : Type uF}…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `ContinuousMultilinearMap.instIsAddApplyForall`：∀ {R : Type u} {ι : Type 
v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → A
ddCommMonoid (M₁ i)] [inst_2 : AddC…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iteratedDerivWithin_add
    (hf : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) :
    iteratedDerivWithin n (f + g) s x =
      iteratedDerivWithin n f s x + iteratedDerivWithin n g s x := by
  simp_rw [iteratedDerivWithin, iteratedFDerivWithin_add_apply hf hg h hx, add_apply]

include h hx in
/-
**iteratedDerivWithin_fun_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDerivWithin_fun_add (hf : ContDiffWithinAt 𝕜 n f s x) (hg : ContDi
ffWithinAt 𝕜 n g s x) : iteratedDerivWithin n (fun z => f z + g z) s x = iterate
dDerivWithin n f s x + iteratedDerivWithin n g s x
参数：hf : ContDiffWithinAt 𝕜 n f s x；hg : ContDiffWithinAt 𝕜 n g s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iteratedDerivWithin_add`：iteratedDerivWithin_add (hf : ContDiffWithinAt 
𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) : iteratedDerivWithin n (f + g) s x
 = iteratedDe…
-/
theorem iteratedDerivWithin_fun_add
    (hf : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) :
    iteratedDerivWithin n (fun z ↦ f z + g z) s x =
      iteratedDerivWithin n f s x + iteratedDerivWithin n g s x := by
  simpa using! iteratedDerivWithin_add hx h hf hg
/-
**iteratedDerivWithin_const_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDerivWithin_const_add (hn : 0 < n) (c : F) : iteratedDerivWithin n
 (fun z => c + f z) s x = iteratedDerivWithin n f s x
参数：hn : 0 < n；c : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.exists_eq_succ_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → ∃ k, n = k.succ
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iteratedDerivWithin_succ'`：iteratedDerivWithin_succ' : iteratedDerivWith
in (n + 1) f s = (iteratedDerivWithin n (derivWithin f s) s)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `derivWithin_const_add`：derivWithin_const_add (c : F) : derivWithin (c + 
f ·) s x = derivWithin f s x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem iteratedDerivWithin_const_add (hn : 0 < n) (c : F) :
    iteratedDerivWithin n (fun z => c + f z) s x = iteratedDerivWithin n f s x := by
  obtain ⟨n, rfl⟩ := n.exists_eq_succ_of_ne_zero hn.ne'
  rw [iteratedDerivWithin_succ', iteratedDerivWithin_succ']
  congr 1 with y
  exact derivWithin_const_add _
/-
**iteratedDerivWithin_const_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDerivWithin_const_sub (hn : 0 < n) (c : F) : iteratedDerivWithin n
 (fun z => c - f z) s x = iteratedDerivWithin n (fun z => -f z) s x
参数：hn : 0 < n；c : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.exists_eq_succ_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → ∃ k, n = k.succ
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iteratedDerivWithin_succ'`：iteratedDerivWithin_succ' : iteratedDerivWith
in (n + 1) f s = (iteratedDerivWithin n (derivWithin f s) s)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `derivWithin.fun_neg`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {
F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {f : 𝕜 
→ F} {x :…
· 使用定理 `derivWithin_const_sub`：derivWithin_const_sub (c : F) : derivWithin (fun 
y => c - f y) s x = -derivWithin f s x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem iteratedDerivWithin_const_sub (hn : 0 < n) (c : F) :
    iteratedDerivWithin n (fun z => c - f z) s x = iteratedDerivWithin n (fun z => -f z) s x := by
  obtain ⟨n, rfl⟩ := n.exists_eq_succ_of_ne_zero hn.ne'
  rw [iteratedDerivWithin_succ', iteratedDerivWithin_succ']
  congr 1 with y
  rw [derivWithin.fun_neg]
  exact derivWithin_const_sub _

include h hx in
/-
**iteratedDerivWithin_const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDerivWithin_const_smul (c : R) (hf : ContDiffWithinAt 𝕜 n f s x) :
 iteratedDerivWithin n (c • f) s x = c • iteratedDerivWithin n f s x
参数：c : R；hf : ContDiffWithinAt 𝕜 n f s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iteratedFDerivWithin_const_smul_apply`：iteratedFDerivWithin_const_smul_a
pply (hf : ContDiffWithinAt 𝕜 i f s x) (hu : UniqueDiffOn 𝕜 s) (hx : x in s) : i
teratedFDerivWithin 𝕜 i (a …
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousMultilinearMap.instIsSMulApplyForall`：∀ {ι : Type v} {M₁ : ι →
 Type w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCo
mmMonoid M₂]   [inst_2 : (i : ι) → T…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iteratedDerivWithin_const_smul (c : R) (hf : ContDiffWithinAt 𝕜 n f s x) :
    iteratedDerivWithin n (c • f) s x = c • iteratedDerivWithin n f s x := by
  simp [iteratedDerivWithin, iteratedFDerivWithin_const_smul_apply hf h hx]

include h hx in
/-
**iteratedDerivWithin_fun_const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDerivWithin_fun_const_smul (c : R) (hf : ContDiffWithinAt 𝕜 n f s 
x) : iteratedDerivWithin n (fun w => c • f w) s x = c • iteratedDerivWithin n f 
s x
参数：c : R；hf : ContDiffWithinAt 𝕜 n f s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iteratedDerivWithin_const_smul`：iteratedDerivWithin_const_smul (c : R) (
hf : ContDiffWithinAt 𝕜 n f s x) : iteratedDerivWithin n (c • f) s x = c • itera
tedDerivWithin n f s…
-/
theorem iteratedDerivWithin_fun_const_smul (c : R) (hf : ContDiffWithinAt 𝕜 n f s x) :
    iteratedDerivWithin n (fun w ↦ c • f w) s x = c • iteratedDerivWithin n f s x :=
  iteratedDerivWithin_const_smul hx h c hf

/-- A variant of `iteratedDerivWithin_const_smul` without differentiability assumption when
the scalar multiplication is by division ring elements. -/
@[simp]
/-
**iteratedDerivWithin_const_smul_field** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDerivWithin_const_smul_field (c : 𝕝) (f : 𝕜 -> F) : iteratedDerivW
ithin n (c • f) s x = c • iteratedDerivWithin n f s x
参数：c : 𝕝；f : 𝕜 -> F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedDerivWithin_zero`：iteratedDerivWithin_zero : iteratedDerivWithin
 0 f s = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iteratedDerivWithin_succ`：iteratedDerivWithin_succ : iteratedDerivWithin
 (n + 1) f s = derivWithin (iteratedDerivWithin n f s) s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `derivWithin_const_smul_field`：derivWithin_const_smul_field (c : 𝕝) (f : 
𝕜 -> F) : derivWithin (c • f) s x = c • derivWithin f s x

--- 原说明 ---
A variant of `iteratedDerivWithin_const_smul` without differentiability assumpti
on when
the scalar multiplication is by division ring elements.
-/
theorem iteratedDerivWithin_const_smul_field (c : 𝕝) (f : 𝕜 → F) :
    iteratedDerivWithin n (c • f) s x = c • iteratedDerivWithin n f s x := by
  induction n generalizing f x with
  | zero => simp
  | succ n IH =>
    simp_rw [iteratedDerivWithin_succ, funext (@IH · f), ← Pi.smul_def,
      derivWithin_const_smul_field]

include h hx in
/-
**iteratedDerivWithin_const_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDerivWithin_const_mul (c : 𝔸) {f : 𝕜 -> 𝔸} (hf : ContDiffWithinAt 
𝕜 n f s x) : iteratedDerivWithin n (fun z => c * f z) s x = c * iteratedDerivWit
hin n f s x
参数：c : 𝔸；hf : ContDiffWithinAt 𝕜 n f s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iteratedDerivWithin_fun_const_smul`：iteratedDerivWithin_fun_const_smul (
c : R) (hf : ContDiffWithinAt 𝕜 n f s x) : iteratedDerivWithin n (fun w => c • f
 w) s x = c • iteratedDe…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
-/
theorem iteratedDerivWithin_const_mul (c : 𝔸) {f : 𝕜 → 𝔸} (hf : ContDiffWithinAt 𝕜 n f s x) :
    iteratedDerivWithin n (fun z => c * f z) s x = c * iteratedDerivWithin n f s x :=
  iteratedDerivWithin_fun_const_smul hx h c hf

/-- A variant of `iteratedDerivWithin_fun_const_smul` without differentiability assumption when
the scalar multiplication is by division ring elements. -/
@[simp]
/-
**iteratedDerivWithin_fun_const_smul_field** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDerivWithin_fun_const_smul_field (c : 𝕝) (f : 𝕜 -> F) : iteratedDe
rivWithin n (fun z => c • f z) s x = c • iteratedDerivWithin n f s x
参数：c : 𝕝；f : 𝕜 -> F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iteratedDerivWithin_const_smul_field`：iteratedDerivWithin_const_smul_fie
ld (c : 𝕝) (f : 𝕜 -> F) : iteratedDerivWithin n (c • f) s x = c • iteratedDerivW
ithin n f s x

--- 原说明 ---
A variant of `iteratedDerivWithin_fun_const_smul` without differentiability assu
mption when
the scalar multiplication is by division ring elements.
-/
theorem iteratedDerivWithin_fun_const_smul_field (c : 𝕝) (f : 𝕜 → F) :
    iteratedDerivWithin n (fun z => c • f z) s x = c • iteratedDerivWithin n f s x :=
  iteratedDerivWithin_const_smul_field c f

@[simp]
/-
**iteratedDerivWithin_const_mul_field** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDerivWithin_const_mul_field (c : 𝕜') (f : 𝕜 -> 𝕜') : iteratedDeriv
Within n (fun z => c * f z) s x = c * iteratedDerivWithin n f s x
参数：c : 𝕜'；f : 𝕜 -> 𝕜'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iteratedDerivWithin_fun_const_smul_field`：iteratedDerivWithin_fun_const_
smul_field (c : 𝕝) (f : 𝕜 -> F) : iteratedDerivWithin n (fun z => c • f z) s x =
 c • iteratedDerivWithin n f s…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
-/
theorem iteratedDerivWithin_const_mul_field (c : 𝕜') (f : 𝕜 → 𝕜') :
    iteratedDerivWithin n (fun z => c * f z) s x = c * iteratedDerivWithin n f s x :=
  iteratedDerivWithin_fun_const_smul_field c f

include h hx in
/-
**iteratedDerivWithin_smul_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDerivWithin_smul_const {f : 𝕜 -> 𝔸} (hf : ContDiffWithinAt 𝕜 n f s
 x) (v : F) : iteratedDerivWithin n (fun y => f y • v) s x = iteratedDerivWithin
 n f s x • v
参数：hf : ContDiffWithinAt 𝕜 n f s x；v : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `iteratedFDerivWithin_smul_const_apply`：iteratedFDerivWithin_smul_const_a
pply {f : E -> A} (hf : ContDiffWithinAt 𝕜 i f s x) (hu : UniqueDiffOn 𝕜 s) (hx 
: x in s) : iteratedFDerivW…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ContinuousLinearMap.compContinuousMultilinearMap_coe`：∀ {R : Type u} {ι 
: Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂} {M₃ : Type w₃} [inst : Semiring R]  
 [inst_1 : (i : ι) → AddCommMonoid (M₁ i)]…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iteratedDerivWithin_smul_const {f : 𝕜 → 𝔸} (hf : ContDiffWithinAt 𝕜 n f s x) (v : F) :
    iteratedDerivWithin n (fun y ↦ f y • v) s x = iteratedDerivWithin n f s x • v := by
  simp [iteratedDerivWithin, iteratedFDerivWithin_smul_const_apply hf h hx]

include h hx in
@[simp]
/-
**iteratedDerivWithin_mul_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDerivWithin_mul_const {f : 𝕜 -> 𝔸} (hf : ContDiffWithinAt 𝕜 n f s 
x) (d : 𝔸) : iteratedDerivWithin n (fun z => f z * d) s x = iteratedDerivWithin 
n f s x * d
参数：hf : ContDiffWithinAt 𝕜 n f s x；d : 𝔸。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iteratedDerivWithin_smul_const`：iteratedDerivWithin_smul_const {f : 𝕜 ->
 𝔸} (hf : ContDiffWithinAt 𝕜 n f s x) (v : F) : iteratedDerivWithin n (fun y => 
f y • v) s x = itera…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem iteratedDerivWithin_mul_const {f : 𝕜 → 𝔸} (hf : ContDiffWithinAt 𝕜 n f s x) (d : 𝔸) :
    iteratedDerivWithin n (fun z ↦ f z * d) s x = iteratedDerivWithin n f s x * d :=
  iteratedDerivWithin_smul_const hx h hf d

/-- A variant of `iteratedDerivWithin_mul_const` without differentiability assumption when
the scalar multiplication is by division ring elements. -/
@[simp]
/-
**iteratedDerivWithin_mul_const_field** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDerivWithin_mul_const_field (f : 𝕜 -> 𝕜') (d : 𝕜') : iteratedDeriv
Within n (fun z => f z * d) s x = iteratedDerivWithin n f s x * d
参数：f : 𝕜 -> 𝕜'；d : 𝕜'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedDerivWithin_zero`：iteratedDerivWithin_zero : iteratedDerivWithin
 0 f s = f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iteratedDerivWithin_succ`：iteratedDerivWithin_succ : iteratedDerivWithin
 (n + 1) f s = derivWithin (iteratedDerivWithin n f s) s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `derivWithin_mul_const_field`：derivWithin_mul_const_field (u : 𝕜') : deri
vWithin (fun y => v y * u) s x = derivWithin v s x * u

--- 原说明 ---
A variant of `iteratedDerivWithin_mul_const` without differentiability assumptio
n when
the scalar multiplication is by division ring elements.
-/
theorem iteratedDerivWithin_mul_const_field (f : 𝕜 → 𝕜') (d : 𝕜') :
    iteratedDerivWithin n (fun z ↦ f z * d) s x = iteratedDerivWithin n f s x * d := by
  induction n generalizing f x with
  | zero => simp
  | succ n IH =>
    simp_rw [iteratedDerivWithin_succ, funext (@IH · f), derivWithin_mul_const_field]

variable (f) in
omit h hx in
@[simp]
/-
**iteratedDerivWithin_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDerivWithin_neg : iteratedDerivWithin n (-f) s x = -iteratedDerivW
ithin n f s x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedDerivWithin_zero`：iteratedDerivWithin_zero : iteratedDerivWithin
 0 f s = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iteratedDerivWithin_succ`：iteratedDerivWithin_succ : iteratedDerivWithin
 (n + 1) f s = derivWithin (iteratedDerivWithin n f s) s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `derivWithin.neg`：derivWithin.neg : derivWithin (-f) s x = -derivWithin f
 s x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem iteratedDerivWithin_neg :
    iteratedDerivWithin n (-f) s x = -iteratedDerivWithin n f s x := by
  induction n generalizing x with
  | zero => simp
  | succ n IH =>
    simp only [iteratedDerivWithin_succ]
    rw [← derivWithin.neg]
    congr with y
    exact IH

variable (f) in
/-
**iteratedDerivWithin_fun_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDerivWithin_fun_neg : iteratedDerivWithin n (fun z => -f z) s x = 
-iteratedDerivWithin n f s x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iteratedDerivWithin_neg`：iteratedDerivWithin_neg : iteratedDerivWithin n
 (-f) s x = -iteratedDerivWithin n f s x
-/
theorem iteratedDerivWithin_fun_neg :
    iteratedDerivWithin n (fun z => -f z) s x = -iteratedDerivWithin n f s x :=
  iteratedDerivWithin_neg f

include h hx
/-
**iteratedDerivWithin_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDerivWithin_sub (hf : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWi
thinAt 𝕜 n g s x) : iteratedDerivWithin n (f - g) s x = iteratedDerivWithin n f 
s x - iteratedDerivWithin n g s x
参数：hf : ContDiffWithinAt 𝕜 n f s x；hg : ContDiffWithinAt 𝕜 n g s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Pi.neg_def`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : (i : ι) → Neg (G
 i)] (f : (i : ι) → G i), -f = fun i => -f i
· 使用定理 `iteratedDerivWithin_add`：iteratedDerivWithin_add (hf : ContDiffWithinAt 
𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) : iteratedDerivWithin n (f + g) s x
 = iteratedDe…
· 使用定理 `ContDiffWithinAt.neg`：ContDiffWithinAt.neg {s : Set E} {f : E -> F} (hf 
: ContDiffWithinAt 𝕜 n f s x) : ContDiffWithinAt 𝕜 n (fun x => -f x) s x
· 使用定理 `iteratedDerivWithin_fun_neg`：iteratedDerivWithin_fun_neg : iteratedDeriv
Within n (fun z => -f z) s x = -iteratedDerivWithin n f s x
-/
theorem iteratedDerivWithin_sub
    (hf : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) :
    iteratedDerivWithin n (f - g) s x =
      iteratedDerivWithin n f s x - iteratedDerivWithin n g s x := by
  rw [sub_eq_add_neg, sub_eq_add_neg, Pi.neg_def, iteratedDerivWithin_add hx h hf hg.neg,
    iteratedDerivWithin_fun_neg]
/-
**iteratedDerivWithin_comp_const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDerivWithin_comp_const_smul (hf : ContDiffOn 𝕜 n f s) (c : 𝕜) (hs 
: Set.MapsTo (c * ·) s s) : iteratedDerivWithin n (fun x => f (c * x)) s x = c ^
 n • iteratedDerivWithin n f s (c * x)
参数：hf : ContDiffOn 𝕜 n f s；c : 𝕜；hs : Set.MapsTo (c * ·) s s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedDerivWithin_zero`：iteratedDerivWithin_zero : iteratedDerivWithin
 0 f s = f
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ContDiffOn.of_succ`：ContDiffOn.of_succ (h : ContDiffOn 𝕜 (n + 1) f s) : 
ContDiffOn 𝕜 n f s
· 使用定理 `ContDiffOn.differentiableOn_iteratedDerivWithin`：ContDiffOn.differentiab
leOn_iteratedDerivWithin {n : Nat∞ω} {m : Nat} (h : ContDiffOn 𝕜 n f s) (hmn : m
 < n) (hs : UniqueDiffOn 𝕜 s) : Diffe…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_lt`：cast_lt : (m : α) < n ↔ m < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `DifferentiableWithinAt.comp`：DifferentiableWithinAt.comp {g : F -> G} {t
 : Set F} (hg : DifferentiableWithinAt 𝕜 g t (f x)) (hf : DifferentiableWithinAt
 𝕜 f s x) (h : Ma…
· 使用定理 `DifferentiableWithinAt.const_mul`：DifferentiableWithinAt.const_mul (ha :
 DifferentiableWithinAt 𝕜 a s x) (b : 𝔸) : DifferentiableWithinAt 𝕜 (fun y => b 
* a y) s x
· 使用定理 `differentiableWithinAt_id`：differentiableWithinAt_id : DifferentiableWit
hinAt 𝕜 id s x
· 使用定理 `iteratedDerivWithin_succ`：iteratedDerivWithin_succ : iteratedDerivWithin
 (n + 1) f s = derivWithin (iteratedDerivWithin n f s) s
· 使用定理 `derivWithin_congr`：derivWithin_congr (hs : EqOn f₁ f s) (hx : f₁ x = f x
) : derivWithin f₁ s x = derivWithin f s x
· 使用定理 `derivWithin_fun_const_smul`：derivWithin_fun_const_smul (c : R) (hf : Dif
ferentiableWithinAt 𝕜 f s x) : derivWithin (fun y => c • f y) s x = c • derivWit
hin f s x
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `derivWithin.scomp`：derivWithin.scomp (hg : DifferentiableWithinAt 𝕜' g₁ 
t' (h x)) (hh : DifferentiableWithinAt 𝕜 h s x) (hs : MapsTo h s t') : derivWith
in (g₁ …
· 使用定理 `derivWithin_const_mul`：derivWithin_const_mul (c : 𝔸) (hd : Differentiabl
eWithinAt 𝕜 d s x) : derivWithin (fun y => c * d y) s x = c * derivWithin d s x
（共 34 条，此处仅展示前 30 条）
-/
theorem iteratedDerivWithin_comp_const_smul (hf : ContDiffOn 𝕜 n f s) (c : 𝕜)
    (hs : Set.MapsTo (c * ·) s s) :
    iteratedDerivWithin n (fun x => f (c * x)) s x = c ^ n • iteratedDerivWithin n f s (c * x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    have hcx : c * x ∈ s := hs hx
    have h₀ : s.EqOn
        (iteratedDerivWithin n (fun x ↦ f (c * x)) s)
        (fun x => c ^ n • iteratedDerivWithin n f s (c * x)) :=
      fun x hx => ih hx hf.of_succ
    have h₁ : DifferentiableWithinAt 𝕜 (iteratedDerivWithin n f s) s (c * x) :=
      hf.differentiableOn_iteratedDerivWithin (Nat.cast_lt.mpr n.lt_succ_self) h _ hcx
    have h₂ : DifferentiableWithinAt 𝕜 (fun x => iteratedDerivWithin n f s (c * x)) s x := by
      rw [← Function.comp_def]
      apply DifferentiableWithinAt.comp _ ?_ (by fun_prop) hs
      exact hf.differentiableOn_iteratedDerivWithin (Nat.cast_lt.mpr n.lt_succ_self) h _ hcx
    rw [iteratedDerivWithin_succ, derivWithin_congr h₀ (ih hx hf.of_succ),
      derivWithin_fun_const_smul (c ^ n) h₂, iteratedDerivWithin_succ,
      ← Function.comp_def, derivWithin.scomp x h₁ (by fun_prop) hs,
      derivWithin_const_mul _ differentiableWithinAt_id, derivWithin_id' _ _ (h _ hx),
      smul_smul, mul_one, pow_succ]

open scoped Pointwise

omit hx h in
/-
**iteratedDerivWithin_comp_neg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iteratedDerivWithin_comp_neg (a : 𝕜) : iteratedDerivWithin n (fun x => f (
-x)) s a = (-1 : 𝕜) ^ n • iteratedDerivWithin n f (-s) (-a)
参数：a : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用引理 `iteratedFDerivWithin_comp_neg`：iteratedFDerivWithin_comp_neg {f : 𝕜 -> F
} {s : Set 𝕜} (n : Nat) (a : 𝕜) : iteratedFDerivWithin 𝕜 n (fun x => f (-x)) s a
 = (-1 : 𝕜) ^ n • i…
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousMultilinearMap.instIsSMulApplyForall`：∀ {ι : Type v} {M₁ : ι →
 Type w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCo
mmMonoid M₂]   [inst_2 : (i : ι) → T…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma iteratedDerivWithin_comp_neg (a : 𝕜) : iteratedDerivWithin n (fun x ↦ f (-x)) s a
    = (-1 : 𝕜) ^ n • iteratedDerivWithin n f (-s) (-a) := by
  simp [iteratedDerivWithin, iteratedFDerivWithin_comp_neg n a]

omit hx h in
/-
**iteratedDerivWithin_comp_const_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDerivWithin_comp_const_add (c : 𝕜) : iteratedDerivWithin n (fun z 
=> f (c + z)) s = fun x => iteratedDerivWithin n f (c +ᵥ s) (c + x)
参数：c : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `iteratedFDerivWithin_comp_add_left`：iteratedFDerivWithin_comp_add_left (
n : Nat) (a : E) (x : E) : iteratedFDerivWithin 𝕜 n (fun z => f (a + z)) s x = i
teratedFDerivWithin 𝕜 n …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iteratedDerivWithin_comp_const_add (c : 𝕜) :
    iteratedDerivWithin n (fun z => f (c + z)) s =
      fun x ↦ iteratedDerivWithin n f (c +ᵥ s) (c + x) := by
  ext x
  simp [iteratedDerivWithin, ← iteratedFDerivWithin_comp_add_left n c x]

omit hx h in
/-
**iteratedDerivWithin_comp_add_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDerivWithin_comp_add_const (c : 𝕜) : iteratedDerivWithin n (fun z 
=> f (z + c)) s = fun x => iteratedDerivWithin n f (c +ᵥ s) (x + c)
参数：c : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `iteratedFDerivWithin_comp_add_right`：iteratedFDerivWithin_comp_add_right
 (n : Nat) (a : E) (x : E) : iteratedFDerivWithin 𝕜 n (fun z => f (z + a)) s x =
 iteratedFDerivWithin 𝕜 n…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iteratedDerivWithin_comp_add_const (c : 𝕜) :
    iteratedDerivWithin n (fun z => f (z + c)) s =
      fun x ↦ iteratedDerivWithin n f (c +ᵥ s) (x + c) := by
  ext x
  simp [iteratedDerivWithin, ← iteratedFDerivWithin_comp_add_right n c x]

omit hx h in
/-
**iteratedDerivWithin_comp_sub_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDerivWithin_comp_sub_const (c : 𝕜) : iteratedDerivWithin n (fun z 
=> f (z - c)) s = fun x => iteratedDerivWithin n f (-c +ᵥ s) (x - c)
参数：c : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `iteratedDerivWithin_comp_add_const`：iteratedDerivWithin_comp_add_const (
c : 𝕜) : iteratedDerivWithin n (fun z => f (z + c)) s = fun x => iteratedDerivWi
thin n f (c +ᵥ s) (x + c…
-/
theorem iteratedDerivWithin_comp_sub_const (c : 𝕜) :
    iteratedDerivWithin n (fun z => f (z - c)) s =
      fun x ↦ iteratedDerivWithin n f (-c +ᵥ s) (x - c) := by
  simpa only [sub_eq_add_neg] using iteratedDerivWithin_comp_add_const (-c)

omit hx h in
/-
**iteratedDerivWithin_comp_const_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDerivWithin_comp_const_sub (c : 𝕜) : iteratedDerivWithin n (fun z 
=> f (c - z)) s = fun x => (-1 : 𝕜) ^ n • iteratedDerivWithin n f (c +ᵥ -s) (c -
 x)
参数：c : 𝕜。
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
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedFDerivWithin_comp_const_sub`：iteratedFDerivWithin_comp_const_sub
 {f : 𝕜 -> F} {s : Set 𝕜} (n : Nat) (c : 𝕜) : iteratedFDerivWithin 𝕜 n (fun z =>
 f (c - z)) s = fun x => …
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousMultilinearMap.instIsSMulApplyForall`：∀ {ι : Type v} {M₁ : ι →
 Type w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCo
mmMonoid M₂]   [inst_2 : (i : ι) → T…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iteratedDerivWithin_comp_const_sub (c : 𝕜) :
    iteratedDerivWithin n (fun z => f (c - z)) s =
      fun x ↦ (-1 : 𝕜) ^ n • iteratedDerivWithin n f (c +ᵥ -s) (c - x) := by
  ext a
  simp [iteratedDerivWithin, iteratedFDerivWithin_comp_const_sub]

@[to_fun iteratedDerivWithin_fun_id]
/-
**iteratedDerivWithin_id** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iteratedDerivWithin_id : iteratedDerivWithin n id s x = if n = 0 then x el
se if n = 1 then 1 else 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedDerivWithin_zero`：iteratedDerivWithin_zero : iteratedDerivWithin
 0 f s = f
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iteratedDerivWithin_succ'`：iteratedDerivWithin_succ' : iteratedDerivWith
in (n + 1) f s = (iteratedDerivWithin n (derivWithin f s) s)
· 使用定理 `iteratedDerivWithin_congr`：iteratedDerivWithin_congr (hfg : Set.EqOn f g
 s) : Set.EqOn (iteratedDerivWithin n f s) (iteratedDerivWithin n g s) s
· 使用定理 `derivWithin_id`：derivWithin_id (hxs : UniqueDiffWithinAt 𝕜 s x) : derivW
ithin id s x = 1
· 使用定理 `UniqueDiffOn.uniqueDiffWithinAt`：UniqueDiffOn.uniqueDiffWithinAt {s : Se
t E} {x} (hs : UniqueDiffOn R s) (h : x in s) : UniqueDiffWithinAt R s x
· 使用定理 `iteratedDerivWithin_const`：iteratedDerivWithin_const {n : Nat} {c : F} {
s : Set 𝕜} {x : 𝕜} : iteratedDerivWithin n (fun _ => c) s x = if n = 0 then c el
se 0
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
-/
lemma iteratedDerivWithin_id :
    iteratedDerivWithin n id s x = if n = 0 then x else if n = 1 then 1 else 0 := by
  obtain (_ | n) := n
  · simp
  · rw [iteratedDerivWithin_succ', iteratedDerivWithin_congr (g := fun _ ↦ 1) _ hx]
    · simp [iteratedDerivWithin_const]
    · exact fun y hy ↦ derivWithin_id _ _ (h.uniqueDiffWithinAt hy)
/-
**iteratedDerivWithin_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iteratedDerivWithin_smul {f : 𝕜 -> 𝔸} {g : 𝕜 -> F} (hf : ContDiffWithinAt 
𝕜 (↑n) f s x) (hg : ContDiffWithinAt 𝕜 (↑n) g s x) : iteratedDerivWithin n (f • 
g) s x = ∑ i in .range (n + 1), n.choose i • iteratedDerivWithin i f s x • itera
tedDerivWithin (n - i) g s x
参数：hf : ContDiffWithinAt 𝕜 (↑n) f s x；hg : ContDiffWithinAt 𝕜 (↑n) g s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedDerivWithin_zero`：iteratedDerivWithin_zero : iteratedDerivWithin
 0 f s = f
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `Nat.choose_self`：choose_self (n : Nat) : choose n n = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.Eventually.exists_mem`：∀ {α : Type u} {p : α → Prop} {f : Filter 
α}, (∀ᶠ (x : α) in f, p x) → ∃ v ∈ f, ∀ y ∈ v, p y
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `ContDiffWithinAt.eventually`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {F : Type uF} […
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iteratedDerivWithin_succ'`：iteratedDerivWithin_succ' : iteratedDerivWith
in (n + 1) f s = (iteratedDerivWithin n (derivWithin f s) s)
· 使用定理 `Filter.EventuallyEq.iteratedDerivWithin_eq_of_nhds_insert`：Filter.Eventu
allyEq.iteratedDerivWithin_eq_of_nhds_insert {𝕜 F : Type*} [NontriviallyNormedFi
eld 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `derivWithin_smul`：derivWithin_smul (hc : DifferentiableWithinAt 𝕜 c s x)
 (hf : DifferentiableWithinAt 𝕜 f s x) : derivWithin (c • f) s x = c x • derivWi
thin f…
· 使用定理 `ContDiffWithinAt.differentiableWithinAt`：ContDiffWithinAt.differentiable
WithinAt (h : ContDiffWithinAt 𝕜 n f s x) (hn : n != 0) : DifferentiableWithinAt
 𝕜 f s x
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `WithTop.canonicallyOrderedAdd`：∀ {α : Type u} [inst : Add α] [inst_1 : P
reorder α] [CanonicallyOrderedAdd α], CanonicallyOrderedAdd (WithTop α)
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
（共 55 条，此处仅展示前 30 条）
-/
lemma iteratedDerivWithin_smul {f : 𝕜 → 𝔸} {g : 𝕜 → F}
    (hf : ContDiffWithinAt 𝕜 (↑n) f s x) (hg : ContDiffWithinAt 𝕜 (↑n) g s x) :
    iteratedDerivWithin n (f • g) s x = ∑ i ∈ .range (n + 1),
      n.choose i • iteratedDerivWithin i f s x • iteratedDerivWithin (n - i) g s x := by
  induction n generalizing f g with
  | zero => simp
  | succ n IH =>
    obtain ⟨U, hU, H⟩ := ((hf.eventually (by simp)).and (hg.eventually (by simp))).exists_mem
    rw [iteratedDerivWithin_succ', Filter.EventuallyEq.iteratedDerivWithin_eq_of_nhds_insert
        (g := f • derivWithin g s + derivWithin f s • g)]
    · rw [Finset.sum_range_succ', iteratedDerivWithin_add hx h, IH, Finset.sum_range_succ', IH]
      · simp only [Nat.choose_succ_succ', add_smul, Finset.sum_add_distrib]
        nth_rw 3 [Finset.sum_range_succ]
        have : ∀ i ∈ Finset.range n, 1 ≤ n - i := by simp; lia
        simp +contextual [← iteratedDerivWithin_succ', ← n.sub_sub, Nat.sub_add_cancel, this]
        abel
      all_goals clear IH H U hU; fun_prop (disch := simp_all)
    · filter_upwards [hf.eventually (by simp), hg.eventually (by simp)] with y hfy hgy
      rw [derivWithin_smul (hfy.differentiableWithinAt _) (hgy.differentiableWithinAt _)]
      all_goals simp
/-
**iteratedDerivWithin_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iteratedDerivWithin_mul {f g : 𝕜 -> 𝔸} (hf : ContDiffWithinAt 𝕜 n f s x) (
hg : ContDiffWithinAt 𝕜 n g s x) : iteratedDerivWithin n (f * g) s x = ∑ i in .r
ange (n + 1), n.choose i * iteratedDerivWithin i f s x * iteratedDerivWithin (n 
- i) g s x
参数：hf : ContDiffWithinAt 𝕜 n f s x；hg : ContDiffWithinAt 𝕜 n g s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `iteratedDerivWithin_smul`：iteratedDerivWithin_smul {f : 𝕜 -> 𝔸} {g : 𝕜 -
> F} (hf : ContDiffWithinAt 𝕜 (↑n) f s x) (hg : ContDiffWithinAt 𝕜 (↑n) g s x) :
 iteratedDeriv…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma iteratedDerivWithin_mul {f g : 𝕜 → 𝔸}
    (hf : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) :
    iteratedDerivWithin n (f * g) s x = ∑ i ∈ .range (n + 1),
      n.choose i * iteratedDerivWithin i f s x * iteratedDerivWithin (n - i) g s x := by
  simp [← smul_eq_mul, iteratedDerivWithin_smul hx h hf hg]
/-
**iteratedDerivWithin_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDerivWithin_pow (m : Nat) (k : Nat) : iteratedDerivWithin k (· ^ m
) s x = m.descFactorial k * x ^ (m - k)
参数：m : Nat；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `iteratedDerivWithin_const`：iteratedDerivWithin_const {n : Nat} {c : F} {
s : Set 𝕜} {x : 𝕜} : iteratedDerivWithin n (fun _ => c) s x = if n = 0 then c el
se 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedDerivWithin_zero`：iteratedDerivWithin_zero : iteratedDerivWithin
 0 f s = f
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用引理 `iteratedDerivWithin_mul`：iteratedDerivWithin_mul {f g : 𝕜 -> 𝔸} (hf : Co
ntDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) : iteratedDerivWithi
n n (f * g) s…
· 使用定理 `ContDiffWithinAt.pow`：ContDiffWithinAt.pow {f : E -> 𝔸} (hf : ContDiffWi
thinAt 𝕜 n f s x) (m : Nat) : ContDiffWithinAt 𝕜 n (fun y => f y ^ m) s x
· 使用定理 `contDiffWithinAt_id`：contDiffWithinAt_id {s x} : ContDiffWithinAt 𝕜 n (i
d : E -> E) s x
· 使用定理 `Nat.succ_descFactorial_succ`：∀ (n k : ℕ), (n + 1).descFactorial (k + 1) 
= (n + 1) * n.descFactorial k
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
（共 90 条，此处仅展示前 30 条）
-/
theorem iteratedDerivWithin_pow (m : ℕ) (k : ℕ) :
    iteratedDerivWithin k (· ^ m) s x = m.descFactorial k * x ^ (m - k) := by
  induction m generalizing k with
  | zero => cases k <;> simp [iteratedDerivWithin_const]
  | succ i IH =>
    obtain (_ | k) := k
    · simp
    simp only [pow_succ]
    refine (iteratedDerivWithin_mul hx h (by fun_prop) (by fun_prop)).trans ?_
    have : ((i + 1).descFactorial (k + 1)) =
        (k + 1) * (i.descFactorial k) + (i.descFactorial (k + 1)) := by
      rw [Nat.succ_descFactorial_succ]
      cases le_or_gt k i <;> simp [Nat.descFactorial, ← add_mul, *]; lia
    obtain hik | hik := le_or_gt i k <;>
      simp +contextual [IH, iteratedDerivWithin_fun_id, h, hx, Finset.sum_range_succ,
        show ∀ x ∈ Finset.range k, k + 1 - x ≠ 0 by simp; lia, -Nat.descFactorial_succ,
        show ∀ x ∈ Finset.range k, k + 1 - x ≠ 1 by simp; lia, this,
        Nat.descFactorial_eq_zero_iff_lt.mpr, hik,
        show k < i → i - k = (i - (k + 1) + 1) by lia]; ring

end

/-- If two functions agree in a neighborhood, then so do their iterated derivatives. -/
/-
**Filter.EventuallyEq.iteratedDeriv** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Eventually
Eq`。
形式化陈述：∀ {𝕜 : Type u_7} [inst : NontriviallyNormedField 𝕜] {F : Type u_8} [inst_1
 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {f₁ f₂ : 𝕜 → F} {x : 𝕜},  
 f₁ =ᶠ[nhds x] f₂ → ∀ (n : ℕ), iteratedDeriv n f₁ =ᶠ[nhds x] iteratedDeriv n f₂
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a

--- 原说明 ---
If two functions agree in a neighborhood, then so do their iterated derivatives.
-/
protected lemma Filter.EventuallyEq.iteratedDeriv
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f₁ f₂ : 𝕜 → F} {x : 𝕜} (h : f₁ =ᶠ[𝓝 x] f₂) (n : ℕ) :
    iteratedDeriv n f₁ =ᶠ[𝓝 x] iteratedDeriv n f₂ := by
  simp_all [← nhdsWithin_univ, ← iteratedDerivWithin_univ, EventuallyEq.iteratedDerivWithin]

@[to_fun iteratedDeriv_fun_add]
/-
**iteratedDeriv_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iteratedDeriv_add (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x) : it
eratedDeriv n (f + g) x = iteratedDeriv n f x + iteratedDeriv n g x
参数：hf : ContDiffAt 𝕜 n f x；hg : ContDiffAt 𝕜 n g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedDerivWithin_univ`：iteratedDerivWithin_univ : iteratedDerivWithin
 n f univ = iteratedDeriv n f
· 使用定理 `iteratedDerivWithin_add`：iteratedDerivWithin_add (hf : ContDiffWithinAt 
𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) : iteratedDerivWithin n (f + g) s x
 = iteratedDe…
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `uniqueDiffOn_univ`：uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E)
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
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
-/
lemma iteratedDeriv_add (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x) :
    iteratedDeriv n (f + g) x = iteratedDeriv n f x + iteratedDeriv n g x := by
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_add (Set.mem_univ _) uniqueDiffOn_univ hf hg
/-
**iteratedDeriv_const_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDeriv_const_add (hn : 0 < n) (c : F) : iteratedDeriv n (fun z => c
 + f z) x = iteratedDeriv n f x
参数：hn : 0 < n；c : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedDerivWithin_const_add`：iteratedDerivWithin_const_add (hn : 0 < n
) (c : F) : iteratedDerivWithin n (fun z => c + f z) s x = iteratedDerivWithin n
 f s x
-/
theorem iteratedDeriv_const_add (hn : 0 < n) (c : F) :
    iteratedDeriv n (fun z => c + f z) x = iteratedDeriv n f x := by
  simpa only [← iteratedDerivWithin_univ] using iteratedDerivWithin_const_add hn c
/-
**iteratedDeriv_const_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDeriv_const_sub (hn : 0 < n) (c : F) : iteratedDeriv n (fun z => c
 - f z) x = iteratedDeriv n (-f) x
参数：hn : 0 < n；c : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedDerivWithin_const_sub`：iteratedDerivWithin_const_sub (hn : 0 < n
) (c : F) : iteratedDerivWithin n (fun z => c - f z) s x = iteratedDerivWithin n
 (fun z => -f z) s …
-/
theorem iteratedDeriv_const_sub (hn : 0 < n) (c : F) :
    iteratedDeriv n (fun z => c - f z) x = iteratedDeriv n (-f) x := by
  simpa only [← iteratedDerivWithin_univ] using! iteratedDerivWithin_const_sub hn c

@[simp]
/-
**iteratedDeriv_fun_neg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iteratedDeriv_fun_neg (n : Nat) (f : 𝕜 -> F) (a : 𝕜) : iteratedDeriv n (fu
n x => -(f x)) a = -(iteratedDeriv n f a)
参数：n : Nat；f : 𝕜 -> F；a : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedDerivWithin_neg`：iteratedDerivWithin_neg : iteratedDerivWithin n
 (-f) s x = -iteratedDerivWithin n f s x
-/
lemma iteratedDeriv_fun_neg (n : ℕ) (f : 𝕜 → F) (a : 𝕜) :
    iteratedDeriv n (fun x ↦ -(f x)) a = -(iteratedDeriv n f a) := by
  simpa only [← iteratedDerivWithin_univ] using! iteratedDerivWithin_neg f

@[simp]
/-
**iteratedDeriv_neg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iteratedDeriv_neg (n : Nat) (f : 𝕜 -> F) (a : 𝕜) : iteratedDeriv n (-f) a 
= -(iteratedDeriv n f a)
参数：n : Nat；f : 𝕜 -> F；a : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedDerivWithin_neg`：iteratedDerivWithin_neg : iteratedDerivWithin n
 (-f) s x = -iteratedDerivWithin n f s x
-/
lemma iteratedDeriv_neg (n : ℕ) (f : 𝕜 → F) (a : 𝕜) :
    iteratedDeriv n (-f) a = -(iteratedDeriv n f a) := by
  simpa only [← iteratedDerivWithin_univ] using iteratedDerivWithin_neg f
attribute [simp] iteratedDeriv_fun_neg

@[to_fun iteratedDeriv_fun_sub]
/-
**iteratedDeriv_sub** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iteratedDeriv_sub (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x) : it
eratedDeriv n (f - g) x = iteratedDeriv n f x - iteratedDeriv n g x
参数：hf : ContDiffAt 𝕜 n f x；hg : ContDiffAt 𝕜 n g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedDerivWithin_univ`：iteratedDerivWithin_univ : iteratedDerivWithin
 n f univ = iteratedDeriv n f
· 使用定理 `iteratedDerivWithin_sub`：iteratedDerivWithin_sub (hf : ContDiffWithinAt 
𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) : iteratedDerivWithin n (f - g) s x
 = iteratedDe…
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `uniqueDiffOn_univ`：uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E)
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
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
-/
lemma iteratedDeriv_sub (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x) :
    iteratedDeriv n (f - g) x = iteratedDeriv n f x - iteratedDeriv n g x := by
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_sub (Set.mem_univ _) uniqueDiffOn_univ hf hg

@[to_fun iteratedDeriv_fun_const_smul]
/-
**iteratedDeriv_const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDeriv_const_smul {n : Nat} {f : 𝕜 -> F} (h : ContDiffAt 𝕜 n f x) (
c : R) : iteratedDeriv n (c • f) x = c • iteratedDeriv n f x
参数：h : ContDiffAt 𝕜 n f x；c : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedDerivWithin_univ`：iteratedDerivWithin_univ : iteratedDerivWithin
 n f univ = iteratedDeriv n f
· 使用定理 `iteratedDerivWithin_const_smul`：iteratedDerivWithin_const_smul (c : R) (
hf : ContDiffWithinAt 𝕜 n f s x) : iteratedDerivWithin n (c • f) s x = c • itera
tedDerivWithin n f s…
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `uniqueDiffOn_univ`：uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E)
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
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
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contDiffWithinAt_univ`：contDiffWithinAt_univ : ContDiffWithinAt 𝕜 n f un
iv x ↔ ContDiffAt 𝕜 n f x
-/
theorem iteratedDeriv_const_smul {n : ℕ} {f : 𝕜 → F} (h : ContDiffAt 𝕜 n f x) (c : R) :
    iteratedDeriv n (c • f) x = c • iteratedDeriv n f x := by
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_const_smul (Set.mem_univ x) uniqueDiffOn_univ
      c (contDiffWithinAt_univ.mpr h)

/-- A variant of `iteratedDeriv_const_smul` without differentiability assumption when
the scalar multiplication is by division ring elements. -/
@[simp]
/-
**iteratedDeriv_const_smul_field** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDeriv_const_smul_field {n : Nat} (c : 𝕝) (f : 𝕜 -> F) : iteratedDe
riv n (c • f) x = c • iteratedDeriv n f x
参数：c : 𝕝；f : 𝕜 -> F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedDerivWithin_univ`：iteratedDerivWithin_univ : iteratedDerivWithin
 n f univ = iteratedDeriv n f
· 使用定理 `iteratedDerivWithin_const_smul_field`：iteratedDerivWithin_const_smul_fie
ld (c : 𝕝) (f : 𝕜 -> F) : iteratedDerivWithin n (c • f) s x = c • iteratedDerivW
ithin n f s x

--- 原说明 ---
A variant of `iteratedDeriv_const_smul` without differentiability assumption whe
n
the scalar multiplication is by division ring elements.
-/
theorem iteratedDeriv_const_smul_field {n : ℕ} (c : 𝕝) (f : 𝕜 → F) :
    iteratedDeriv n (c • f) x = c • iteratedDeriv n f x := by
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_const_smul_field (s := Set.univ) c f

/-- A variant of `iteratedDeriv_fun_const_smul` without differentiability assumption when
the scalar multiplication is by division ring elements. -/
@[simp]
/-
**iteratedDeriv_fun_const_smul_field** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDeriv_fun_const_smul_field {n : Nat} (c : 𝕝) (f : 𝕜 -> F) : iterat
edDeriv n (c • f ·) x = c • iteratedDeriv n f x
参数：c : 𝕝；f : 𝕜 -> F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedDerivWithin_univ`：iteratedDerivWithin_univ : iteratedDerivWithin
 n f univ = iteratedDeriv n f
· 使用定理 `iteratedDerivWithin_fun_const_smul_field`：iteratedDerivWithin_fun_const_
smul_field (c : 𝕝) (f : 𝕜 -> F) : iteratedDerivWithin n (fun z => c • f z) s x =
 c • iteratedDerivWithin n f s…

--- 原说明 ---
A variant of `iteratedDeriv_fun_const_smul` without differentiability assumption
 when
the scalar multiplication is by division ring elements.
-/
theorem iteratedDeriv_fun_const_smul_field {n : ℕ} (c : 𝕝) (f : 𝕜 → F) :
    iteratedDeriv n (c • f ·) x = c • iteratedDeriv n f x := by
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_fun_const_smul_field (s := Set.univ) c f
/-
**iteratedDeriv_smul_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDeriv_smul_const {f : 𝕜 -> 𝔸} (hf : ContDiffAt 𝕜 n f x) (v : F) : 
iteratedDeriv n (fun y => f y • v) x = iteratedDeriv n f x • v
参数：hf : ContDiffAt 𝕜 n f x；v : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `iteratedFDeriv_smul_const_apply`：iteratedFDeriv_smul_const_apply {f : E 
-> A} (hf : ContDiffAt 𝕜 i f x) : iteratedFDeriv 𝕜 i (fun y => f y • v) x = ((Co
ntinuousLinearMap.id …
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ContinuousLinearMap.compContinuousMultilinearMap_coe`：∀ {R : Type u} {ι 
: Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂} {M₃ : Type w₃} [inst : Semiring R]  
 [inst_1 : (i : ι) → AddCommMonoid (M₁ i)]…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iteratedDeriv_smul_const {f : 𝕜 → 𝔸} (hf : ContDiffAt 𝕜 n f x) (v : F) :
    iteratedDeriv n (fun y ↦ f y • v) x = iteratedDeriv n f x • v := by
  simp [iteratedDeriv, iteratedFDeriv_smul_const_apply hf]
/-
**iteratedDeriv_const_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDeriv_const_mul {n : Nat} {f : 𝕜 -> 𝔸} (c : 𝔸) (hf : ContDiffAt 𝕜 
n f x) : iteratedDeriv n (c * f ·) x = c * iteratedDeriv n f x
参数：c : 𝔸；hf : ContDiffAt 𝕜 n f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedDerivWithin_univ`：iteratedDerivWithin_univ : iteratedDerivWithin
 n f univ = iteratedDeriv n f
· 使用定理 `iteratedDerivWithin_const_mul`：iteratedDerivWithin_const_mul (c : 𝔸) {f 
: 𝕜 -> 𝔸} (hf : ContDiffWithinAt 𝕜 n f s x) : iteratedDerivWithin n (fun z => c 
* f z) s x = c * it…
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `uniqueDiffOn_univ`：uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E)
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
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
-/
theorem iteratedDeriv_const_mul {n : ℕ} {f : 𝕜 → 𝔸} (c : 𝔸) (hf : ContDiffAt 𝕜 n f x) :
    iteratedDeriv n (c * f ·) x = c * iteratedDeriv n f x := by
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_const_mul (Set.mem_univ x) uniqueDiffOn_univ c hf

/-- A variant of `iteratedDeriv_const_mul` without differentiability assumption when
the multiplication is in a division ring. -/
@[simp]
/-
**iteratedDeriv_const_mul_field** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDeriv_const_mul_field {n : Nat} (c : 𝕜') (f : 𝕜 -> 𝕜') : iteratedD
eriv n (c * f ·) x = c * iteratedDeriv n f x
参数：c : 𝕜'；f : 𝕜 -> 𝕜'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedDerivWithin_univ`：iteratedDerivWithin_univ : iteratedDerivWithin
 n f univ = iteratedDeriv n f
· 使用定理 `iteratedDerivWithin_const_mul_field`：iteratedDerivWithin_const_mul_field
 (c : 𝕜') (f : 𝕜 -> 𝕜') : iteratedDerivWithin n (fun z => c * f z) s x = c * ite
ratedDerivWithin n f s x

--- 原说明 ---
A variant of `iteratedDeriv_const_mul` without differentiability assumption when
the multiplication is in a division ring.
-/
theorem iteratedDeriv_const_mul_field {n : ℕ} (c : 𝕜') (f : 𝕜 → 𝕜') :
    iteratedDeriv n (c * f ·) x = c * iteratedDeriv n f x := by
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_const_mul_field (s := .univ) c f

/-- A variant of `iteratedDeriv_mul_const` without differentiability assumption when
the multiplication is in a division ring. -/
@[simp]
/-
**iteratedDeriv_mul_const_field** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDeriv_mul_const_field {n : Nat} (f : 𝕜 -> 𝕜') (c : 𝕜') : iteratedD
eriv n (f · * c) x = iteratedDeriv n f x * c
参数：f : 𝕜 -> 𝕜'；c : 𝕜'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedDerivWithin_univ`：iteratedDerivWithin_univ : iteratedDerivWithin
 n f univ = iteratedDeriv n f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iteratedDerivWithin_mul_const_field`：iteratedDerivWithin_mul_const_field
 (f : 𝕜 -> 𝕜') (d : 𝕜') : iteratedDerivWithin n (fun z => f z * d) s x = iterate
dDerivWithin n f s x * d

--- 原说明 ---
A variant of `iteratedDeriv_mul_const` without differentiability assumption when
the multiplication is in a division ring.
-/
theorem iteratedDeriv_mul_const_field {n : ℕ} (f : 𝕜 → 𝕜') (c : 𝕜') :
    iteratedDeriv n (f · * c) x = iteratedDeriv n f x * c := by
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_mul_const_field (s := .univ) f c

@[simp]
/-
**iteratedDeriv_div_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDeriv_div_const {n : Nat} (f : 𝕜 -> 𝕜') (c : 𝕜') : iteratedDeriv n
 (f · / c) x = iteratedDeriv n f x / c
参数：f : 𝕜 -> 𝕜'；c : 𝕜'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `iteratedDeriv_mul_const_field`：iteratedDeriv_mul_const_field {n : Nat} (
f : 𝕜 -> 𝕜') (c : 𝕜') : iteratedDeriv n (f · * c) x = iteratedDeriv n f x * c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iteratedDeriv_div_const {n : ℕ} (f : 𝕜 → 𝕜') (c : 𝕜') :
    iteratedDeriv n (f · / c) x = iteratedDeriv n f x / c := by
  simp [div_eq_mul_inv]
/-
**iteratedDeriv_comp_const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDeriv_comp_const_smul {n : Nat} {f : 𝕜 -> F} (h : ContDiff 𝕜 n f) 
(c : 𝕜) : iteratedDeriv n (fun x => f (c * x)) = fun x => c ^ n • iteratedDeriv 
n f (c * x)
参数：h : ContDiff 𝕜 n f；c : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedDerivWithin_univ`：iteratedDerivWithin_univ : iteratedDerivWithin
 n f univ = iteratedDeriv n f
· 使用定理 `iteratedDerivWithin_comp_const_smul`：iteratedDerivWithin_comp_const_smul
 (hf : ContDiffOn 𝕜 n f s) (c : 𝕜) (hs : Set.MapsTo (c * ·) s s) : iteratedDeriv
Within n (fun x => f (c *…
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `uniqueDiffOn_univ`：uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E)
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
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
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contDiffOn_univ`：contDiffOn_univ : ContDiffOn 𝕜 n f univ ↔ ContDiff 𝕜 n 
f
· 使用定理 `Set.mapsTo_univ`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (s : Set α)
, Set.MapsTo f s Set.univ
-/
theorem iteratedDeriv_comp_const_smul {n : ℕ} {f : 𝕜 → F} (h : ContDiff 𝕜 n f) (c : 𝕜) :
    iteratedDeriv n (fun x => f (c * x)) = fun x => c ^ n • iteratedDeriv n f (c * x) := by
  funext x
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_comp_const_smul (Set.mem_univ x) uniqueDiffOn_univ (contDiffOn_univ.mpr h)
      c (Set.mapsTo_univ _ _)
/-
**iteratedDeriv_comp_const_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDeriv_comp_const_mul {n : Nat} {f : 𝕜 -> 𝕜} (h : ContDiff 𝕜 n f) (
c : 𝕜) : iteratedDeriv n (fun x => f (c * x)) = fun x => c ^ n * iteratedDeriv n
 f (c * x)
参数：h : ContDiff 𝕜 n f；c : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iteratedDeriv_comp_const_smul`：iteratedDeriv_comp_const_smul {n : Nat} {
f : 𝕜 -> F} (h : ContDiff 𝕜 n f) (c : 𝕜) : iteratedDeriv n (fun x => f (c * x)) 
= fun x => c ^ n • …
-/
theorem iteratedDeriv_comp_const_mul {n : ℕ} {f : 𝕜 → 𝕜} (h : ContDiff 𝕜 n f) (c : 𝕜) :
    iteratedDeriv n (fun x => f (c * x)) = fun x => c ^ n * iteratedDeriv n f (c * x) := by
  simpa only [smul_eq_mul] using iteratedDeriv_comp_const_smul h c
/-
**iteratedDeriv_comp_neg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iteratedDeriv_comp_neg (n : Nat) (f : 𝕜 -> F) (a : 𝕜) : iteratedDeriv n (f
un x => f (-x)) a = (-1 : 𝕜) ^ n • iteratedDeriv n f (-a)
参数：n : Nat；f : 𝕜 -> F；a : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `iteratedFDerivWithin_comp_neg`：iteratedFDerivWithin_comp_neg {f : 𝕜 -> F
} {s : Set 𝕜} (n : Nat) (a : 𝕜) : iteratedFDerivWithin 𝕜 n (fun x => f (-x)) s a
 = (-1 : 𝕜) ^ n • i…
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousMultilinearMap.instIsSMulApplyForall`：∀ {ι : Type v} {M₁ : ι →
 Type w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCo
mmMonoid M₂]   [inst_2 : (i : ι) → T…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma iteratedDeriv_comp_neg (n : ℕ) (f : 𝕜 → F) (a : 𝕜) :
    iteratedDeriv n (fun x ↦ f (-x)) a = (-1 : 𝕜) ^ n • iteratedDeriv n f (-a) := by
  simp [iteratedDeriv, ← iteratedFDerivWithin_univ, iteratedFDerivWithin_comp_neg]

@[to_fun iteratedDeriv_fun_id]
/-
**iteratedDeriv_id** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iteratedDeriv_id {n : Nat} {x : 𝕜} : iteratedDeriv n id x = if n = 0 then 
x else if n = 1 then 1 else 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedDeriv_zero`：iteratedDeriv_zero : iteratedDeriv 0 f = f
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `iteratedDeriv_succ'`：iteratedDeriv_succ' : iteratedDeriv (n + 1) f = ite
ratedDeriv n (deriv f)
· 使用定理 `deriv_id'`：deriv_id' : deriv (@id 𝕜) = fun _ => 1
· 使用定理 `iteratedDeriv_const`：iteratedDeriv_const {n : Nat} {c : F} {x : 𝕜} : ite
ratedDeriv n (fun _ => c) x = if n = 0 then c else 0
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma iteratedDeriv_id {n : ℕ} {x : 𝕜} :
    iteratedDeriv n id x = if n = 0 then x else if n = 1 then 1 else 0 := by
  obtain (_ | _ | n) := n <;>
    simp [iteratedDeriv_succ', iteratedDeriv_const]
/-
**iteratedDeriv_fun_id_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iteratedDeriv_fun_id_zero : iteratedDeriv n (fun a => a) (0 : 𝕜) = if n = 
1 then 1 else 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iteratedDeriv_fun_id`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜
] {n : ℕ} {x : 𝕜},   iteratedDeriv n (fun x => x) x = if n = 0 then x else if n 
= 1 then 1…
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma iteratedDeriv_fun_id_zero :
    iteratedDeriv n (fun a ↦ a) (0 : 𝕜) = if n = 1 then 1 else 0 := by
  simp +contextual [iteratedDeriv_fun_id]

@[to_fun iteratedDeriv_fun_mul]
/-
**iteratedDeriv_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iteratedDeriv_mul {f g : 𝕜 -> 𝔸} (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffA
t 𝕜 n g x) : iteratedDeriv n (f * g) x = ∑ i in .range (n + 1), n.choose i * ite
ratedDeriv i f x * iteratedDeriv (n - i) g x
参数：hf : ContDiffAt 𝕜 n f x；hg : ContDiffAt 𝕜 n g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedDerivWithin_univ`：iteratedDerivWithin_univ : iteratedDerivWithin
 n f univ = iteratedDeriv n f
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `iteratedDerivWithin_mul`：iteratedDerivWithin_mul {f g : 𝕜 -> 𝔸} (hf : Co
ntDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) : iteratedDerivWithi
n n (f * g) s…
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `uniqueDiffOn_univ`：uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E)
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
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
· 使用定理 `ContDiffAt.contDiffWithinAt`：ContDiffAt.contDiffWithinAt (h : ContDiffAt
 𝕜 n f x) : ContDiffWithinAt 𝕜 n f s x
-/
lemma iteratedDeriv_mul {f g : 𝕜 → 𝔸} (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x) :
    iteratedDeriv n (f * g) x = ∑ i ∈ .range (n + 1),
      n.choose i * iteratedDeriv i f x * iteratedDeriv (n - i) g x := by
  simpa using iteratedDerivWithin_mul
    (Set.mem_univ x) uniqueDiffOn_univ hf.contDiffWithinAt hg.contDiffWithinAt

@[simp]
/-
**iteratedDeriv_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDeriv_pow (m : Nat) (k : Nat) : iteratedDeriv k (· ^ m) x = m.desc
Factorial k * x ^ (m - k)
参数：m : Nat；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedDerivWithin_univ`：iteratedDerivWithin_univ : iteratedDerivWithin
 n f univ = iteratedDeriv n f
· 使用定理 `iteratedDerivWithin_pow`：iteratedDerivWithin_pow (m : Nat) (k : Nat) : i
teratedDerivWithin k (· ^ m) s x = m.descFactorial k * x ^ (m - k)
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `uniqueDiffOn_univ`：uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E)
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
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
-/
theorem iteratedDeriv_pow (m : ℕ) (k : ℕ) :
    iteratedDeriv k (· ^ m) x = m.descFactorial k * x ^ (m - k) := by
  simpa using iteratedDerivWithin_pow (Set.mem_univ x) uniqueDiffOn_univ m k
/-
**iteratedDeriv_fun_pow_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iteratedDeriv_fun_pow_zero {n m : Nat} : iteratedDeriv n (· ^ m) (0 : 𝕜) =
 if n = m then m.factorial else 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iteratedDeriv_pow`：iteratedDeriv_pow (m : Nat) (k : Nat) : iteratedDeriv
 k (· ^ m) x = m.descFactorial k * x ^ (m - k)
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.descFactorial_self`：∀ (n : ℕ), n.descFactorial n = n.factorial
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.descFactorial_eq_zero_iff_lt`：∀ {n k : ℕ}, n.descFactorial k = 0 ↔ n
 < k
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
lemma iteratedDeriv_fun_pow_zero {n m : ℕ} :
    iteratedDeriv n (· ^ m) (0 : 𝕜) = if n = m then m.factorial else 0 := by
  obtain h | h | h := lt_trichotomy n m <;>
    simp_all [Nat.descFactorial_self, Nat.descFactorial_eq_zero_iff_lt.mpr, ne_of_lt, ne_of_gt]
/-
**Filter.EventuallyEq.iteratedDeriv_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.iteratedDeriv_eq (n : Nat) {f g : 𝕜 -> F} {x : 𝕜} (hfg
 : f =ᶠ[𝓝 x] g) : iteratedDeriv n f x = iteratedDeriv n g x
参数：n : Nat；hfg : f =ᶠ[𝓝 x] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Filter.EventuallyEq.iteratedFDerivWithin_eq`：Filter.EventuallyEq.iterate
dFDerivWithin_eq (h : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) (n : Nat) : iteratedFDe
rivWithin 𝕜 n f₁ s x = iteratedFD…
· 使用定理 `Filter.EventuallyEq.filter_mono`：∀ {α : Type u} {β : Type v} {l l' : Fil
ter α} {f g : α → β}, f =ᶠ[l] g → l' ≤ l → f =ᶠ[l'] g
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `Filter.EventuallyEq.eq_of_nhds`：Filter.EventuallyEq.eq_of_nhds {f g : X 
-> α} (h : f =ᶠ[𝓝 x] g) : f x = g x
-/
lemma Filter.EventuallyEq.iteratedDeriv_eq (n : ℕ) {f g : 𝕜 → F} {x : 𝕜} (hfg : f =ᶠ[𝓝 x] g) :
    iteratedDeriv n f x = iteratedDeriv n g x := by
  simp only [← iteratedDerivWithin_univ, iteratedDerivWithin_eq_iteratedFDerivWithin]
  rw [(hfg.filter_mono nhdsWithin_le_nhds).iteratedFDerivWithin_eq hfg.eq_of_nhds n]
/-
**Set.EqOn.iteratedDeriv_of_isOpen** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Set.EqOn.iteratedDeriv_of_isOpen (hfg : Set.EqOn f g s) (hs : IsOpen s) (n
 : Nat) : Set.EqOn (iteratedDeriv n f) (iteratedDeriv n g) s
参数：hfg : Set.EqOn f g s；hs : IsOpen s；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Filter.EventuallyEq.iteratedDeriv_eq`：Filter.EventuallyEq.iteratedDeriv_
eq (n : Nat) {f g : 𝕜 -> F} {x : 𝕜} (hfg : f =ᶠ[𝓝 x] g) : iteratedDeriv n f x = 
iteratedDeriv n g x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
-/
lemma Set.EqOn.iteratedDeriv_of_isOpen (hfg : Set.EqOn f g s) (hs : IsOpen s) (n : ℕ) :
    Set.EqOn (iteratedDeriv n f) (iteratedDeriv n g) s := by
  refine fun x hx ↦ Filter.EventuallyEq.iteratedDeriv_eq n ?_
  filter_upwards [IsOpen.mem_nhds hs hx] with a ha
  exact hfg ha

end one_dimensional

/-!
### Invariance of iterated derivatives under translation
-/

section shift_invariance

variable (n : ℕ) (f : 𝕜 → F) (s : 𝕜)

/-- The iterated derivative commutes with shifting the function by a constant on the left. -/
/-
**iteratedDeriv_comp_const_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iteratedDeriv_comp_const_add : iteratedDeriv n (fun z => f (s + z)) = fun 
t => iteratedDeriv n f (s + t)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iteratedDeriv_zero`：iteratedDeriv_zero : iteratedDeriv 0 f = f
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iteratedDeriv_succ`：iteratedDeriv_succ : iteratedDeriv (n + 1) f = deriv
 (iteratedDeriv n f)
· 使用引理 `deriv_comp_const_add`：deriv_comp_const_add : deriv (fun x => f (a + x)) 
x = deriv f (a + x)

--- 原说明 ---
The iterated derivative commutes with shifting the function by a constant on the
 left.
-/
lemma iteratedDeriv_comp_const_add :
    iteratedDeriv n (fun z ↦ f (s + z)) = fun t ↦ iteratedDeriv n f (s + t) := by
  induction n with
  | zero => simp only [iteratedDeriv_zero]
  | succ n IH =>
    simpa only [iteratedDeriv_succ, IH] using funext <| deriv_comp_const_add _ s

/-- The iterated derivative commutes with shifting the function by a constant on the right. -/
/-
**iteratedDeriv_comp_add_const** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iteratedDeriv_comp_add_const : iteratedDeriv n (fun z => f (z + s)) = fun 
t => iteratedDeriv n f (t + s)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iteratedDeriv_zero`：iteratedDeriv_zero : iteratedDeriv 0 f = f
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iteratedDeriv_succ`：iteratedDeriv_succ : iteratedDeriv (n + 1) f = deriv
 (iteratedDeriv n f)
· 使用引理 `deriv_comp_add_const`：deriv_comp_add_const : deriv (fun x => f (x + a)) 
x = deriv f (x + a)

--- 原说明 ---
The iterated derivative commutes with shifting the function by a constant on the
 right.
-/
lemma iteratedDeriv_comp_add_const :
    iteratedDeriv n (fun z ↦ f (z + s)) = fun t ↦ iteratedDeriv n f (t + s) := by
  induction n with
  | zero => simp only [iteratedDeriv_zero]
  | succ n IH =>
    simpa only [iteratedDeriv_succ, IH] using funext <| deriv_comp_add_const _ s
/-
**iteratedDeriv_comp_sub_const** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iteratedDeriv_comp_sub_const : iteratedDeriv n (fun z => f (z - s)) = fun 
t => iteratedDeriv n f (t - s)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用引理 `iteratedDeriv_comp_add_const`：iteratedDeriv_comp_add_const : iteratedDer
iv n (fun z => f (z + s)) = fun t => iteratedDeriv n f (t + s)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma iteratedDeriv_comp_sub_const :
    iteratedDeriv n (fun z ↦ f (z - s)) = fun t ↦ iteratedDeriv n f (t - s) := by
  simp [sub_eq_add_neg, iteratedDeriv_comp_add_const]
/-
**iteratedDeriv_comp_const_sub** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iteratedDeriv_comp_const_sub : iteratedDeriv n (fun z => f (s - z)) = fun 
t => (-1 : 𝕜) ^ n • iteratedDeriv n f (s - t)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `neg_add_eq_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b :
 α), -a + b = b - a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `iteratedDeriv_comp_add_const`：iteratedDeriv_comp_add_const : iteratedDer
iv n (fun z => f (z + s)) = fun t => iteratedDeriv n f (t + s)
· 使用引理 `iteratedDeriv_comp_neg`：iteratedDeriv_comp_neg (n : Nat) (f : 𝕜 -> F) (a
 : 𝕜) : iteratedDeriv n (fun x => f (-x)) a = (-1 : 𝕜) ^ n • iteratedDeriv n f (
-a)
-/
lemma iteratedDeriv_comp_const_sub :
    iteratedDeriv n (fun z ↦ f (s - z)) = fun t ↦ (-1 : 𝕜) ^ n • iteratedDeriv n f (s - t) := by
  simpa [funext_iff, neg_add_eq_sub, iteratedDeriv_comp_add_const] using
    iteratedDeriv_comp_neg n (fun z => f (z + s))

end shift_invariance

section sums

/-!
### Iterated derivatives of sums
-/
open Finset
variable {ι : Type*} {n : ℕ} {x : 𝕜} {f : ι → 𝕜 → F} {I : Finset ι}

/-
**iteratedDerivWithin_sum** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iteratedDerivWithin_sum {s : Set 𝕜} (hx : x in s) (hs : UniqueDiffOn 𝕜 s) 
(hf : forall i in I, ContDiffWithinAt 𝕜 n (f i) s x) : iteratedDerivWithin n (∑ 
i in I, f i) s x = ∑ i in I, iteratedDerivWithin n (f i) s x
参数：hx : x in s；hs : UniqueDiffOn 𝕜 s；hf : forall i in I, ContDiffWithinAt 𝕜 n (f
 i) s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `iteratedDerivWithin_const_zero`：iteratedDerivWithin_const_zero {s : Set 
𝕜} : iteratedDerivWithin n (0 : 𝕜 -> F) s x = (0 : F)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `Finset.sum_fn`：∀ {α : Type u_7} {M : α → Type u_8} {ι : Type u_9} [inst 
: (a : α) → AddCommMonoid (M a)] (s : Finset ι)   (g : ι → (a : α) → M a), ∑ c ∈
 s,…
· 使用定理 `iteratedDerivWithin_add`：iteratedDerivWithin_add (hf : ContDiffWithinAt 
𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) : iteratedDerivWithin n (f + g) s x
 = iteratedDe…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.forall_mem_insert`：forall_mem_insert (a : α) (s : Finset α) (p : 
α -> Prop) : (forall x, x in insert a s -> p x) ↔ p a ∧ forall x, x in s -> p x
· 使用定理 `ContDiffWithinAt.sum`：ContDiffWithinAt.sum {ι : Type*} {f : ι -> E -> F}
 {s : Finset ι} {t : Set E} {x : E} (h : forall i in s, ContDiffWithinAt 𝕜 n (fu
n x => f i…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
lemma iteratedDerivWithin_sum {s : Set 𝕜} (hx : x ∈ s) (hs : UniqueDiffOn 𝕜 s)
    (hf : ∀ i ∈ I, ContDiffWithinAt 𝕜 n (f i) s x) :
    iteratedDerivWithin n (∑ i ∈ I, f i) s x =
      ∑ i ∈ I, iteratedDerivWithin n (f i) s x := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | insert i t hi IH =>
    rw [forall_mem_insert] at hf
    simp only [sum_insert hi, sum_fn] at IH ⊢
    rw [iteratedDerivWithin_add hx hs hf.1 (.sum hf.2), IH hf.2]
/-
**iteratedDerivWithin_fun_sum** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iteratedDerivWithin_fun_sum {s : Set 𝕜} (hx : x in s) (hs : UniqueDiffOn 𝕜
 s) (hf : forall i in I, ContDiffWithinAt 𝕜 n (f i) s x) : iteratedDerivWithin n
 (∑ i in I, f i ·) s x = ∑ i in I, iteratedDerivWithin n (f i) s x
参数：hx : x in s；hs : UniqueDiffOn 𝕜 s；hf : forall i in I, ContDiffWithinAt 𝕜 n (f
 i) s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_fn`：∀ {α : Type u_7} {M : α → Type u_8} {ι : Type u_9} [inst 
: (a : α) → AddCommMonoid (M a)] (s : Finset ι)   (g : ι → (a : α) → M a), ∑ c ∈
 s,…
· 使用引理 `iteratedDerivWithin_sum`：iteratedDerivWithin_sum {s : Set 𝕜} (hx : x in 
s) (hs : UniqueDiffOn 𝕜 s) (hf : forall i in I, ContDiffWithinAt 𝕜 n (f i) s x) 
: iteratedDer…
-/
lemma iteratedDerivWithin_fun_sum {s : Set 𝕜} (hx : x ∈ s) (hs : UniqueDiffOn 𝕜 s)
    (hf : ∀ i ∈ I, ContDiffWithinAt 𝕜 n (f i) s x) :
    iteratedDerivWithin n (∑ i ∈ I, f i ·) s x = ∑ i ∈ I, iteratedDerivWithin n (f i) s x := by
  simpa [sum_fn] using iteratedDerivWithin_sum hx hs hf
/-
**iteratedDeriv_sum** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iteratedDeriv_sum (hf : forall i in I, ContDiffAt 𝕜 n (f i) x) : iteratedD
eriv n (∑ i in I, f i) x = ∑ i in I, iteratedDeriv n (f i) x
参数：hf : forall i in I, ContDiffAt 𝕜 n (f i) x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedDerivWithin_univ`：iteratedDerivWithin_univ : iteratedDerivWithin
 n f univ = iteratedDeriv n f
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `iteratedDerivWithin_sum`：iteratedDerivWithin_sum {s : Set 𝕜} (hx : x in 
s) (hs : UniqueDiffOn 𝕜 s) (hf : forall i in I, ContDiffWithinAt 𝕜 n (f i) s x) 
: iteratedDer…
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `uniqueDiffOn_univ`：uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E)
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
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
-/
lemma iteratedDeriv_sum (hf : ∀ i ∈ I, ContDiffAt 𝕜 n (f i) x) :
    iteratedDeriv n (∑ i ∈ I, f i) x = ∑ i ∈ I, iteratedDeriv n (f i) x := by
  simpa using iteratedDerivWithin_sum (Set.mem_univ x) uniqueDiffOn_univ hf
/-
**iteratedDeriv_fun_sum** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iteratedDeriv_fun_sum (hf : forall i in I, ContDiffAt 𝕜 n (f i) x) : itera
tedDeriv n (fun z => ∑ i in I, f i z) x = ∑ i in I, iteratedDeriv n (f i) x
参数：hf : forall i in I, ContDiffAt 𝕜 n (f i) x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_fn`：∀ {α : Type u_7} {M : α → Type u_8} {ι : Type u_9} [inst 
: (a : α) → AddCommMonoid (M a)] (s : Finset ι)   (g : ι → (a : α) → M a), ∑ c ∈
 s,…
· 使用引理 `iteratedDeriv_sum`：iteratedDeriv_sum (hf : forall i in I, ContDiffAt 𝕜 n
 (f i) x) : iteratedDeriv n (∑ i in I, f i) x = ∑ i in I, iteratedDeriv n (f i) 
x
-/
lemma iteratedDeriv_fun_sum (hf : ∀ i ∈ I, ContDiffAt 𝕜 n (f i) x) :
    iteratedDeriv n (fun z ↦ ∑ i ∈ I, f i z) x = ∑ i ∈ I, iteratedDeriv n (f i) x := by
  simpa [sum_fn] using iteratedDeriv_sum hf

end sums

