/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn, Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Basic

/-!
## Smoothness of standard maps associated to the product of manifolds

This file contains results about smoothness of standard maps associated to products and sums
(disjoint unions) of smooth manifolds:
- if `f` and `g` are `C^n`, so is their point-wise product.
- the component projections from a product of manifolds are smooth.
- functions into a product (*pi type*) are `C^n` iff their components are
- if `M` and `N` are manifolds modelled over the same space, `Sum.inl` and `Sum.inr` are
  `C^n`, as are `Sum.elim`, `Sum.map` and `Sum.swap`.

-/

assert_not_exists mfderiv

public section

open Set Function Filter ChartedSpace

open scoped Topology Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  -- declare a charted space `M` over the pair `(E, H)`.
  {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  -- declare a charted space `M'` over the pair `(E', H')`.
  {E' : Type*}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  -- declare a charted space `N` over the pair `(F, G)`.
  {F : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type*} [TopologicalSpace G]
  {J : ModelWithCorners 𝕜 F G} {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  -- declare a charted space `N'` over the pair `(F', G')`.
  {F' : Type*}
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] {G' : Type*} [TopologicalSpace G']
  {J' : ModelWithCorners 𝕜 F' G'} {N' : Type*} [TopologicalSpace N'] [ChartedSpace G' N']
  -- declare a few vector spaces
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  -- declare functions, sets, points and smoothness indices
  {f : M → M'} {s : Set M} {x : M} {n : WithTop ℕ∞}

section ProdMk

/-
**ContMDiffWithinAt.prodMk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffWithinAt.prodMk {f : M -> M'} {g : M -> N'} (hf : ContMDiffWithin
At I I' n f s x) (hg : ContMDiffWithinAt I J' n g s x) : ContMDiffWithinAt I (I'
.prod J') n (fun x => (f x, g x)) s x
参数：hf : ContMDiffWithinAt I I' n f s x；hg : ContMDiffWithinAt I J' n g s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `contMDiffWithinAt_iff`：contMDiffWithinAt_iff : ContMDiffWithinAt I I' n 
f s x ↔ ContinuousWithinAt f s x ∧ ContDiffWithinAt 𝕜 n (extChartAt I' (f x) ∘ f
 ∘ (extChar…
· 使用定理 `ContinuousWithinAt.prodMk`：ContinuousWithinAt.prodMk {f : α -> β} {g : α
 -> γ} {s : Set α} {x : α} (hf : ContinuousWithinAt f s x) (hg : ContinuousWithi
nAt g s x) : Co…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ContDiffWithinAt.prodMk`：ContDiffWithinAt.prodMk {s : Set E} {f : E -> F
} {g : E -> G} (hf : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s 
x) : ContDiff…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem ContMDiffWithinAt.prodMk {f : M → M'} {g : M → N'} (hf : ContMDiffWithinAt I I' n f s x)
    (hg : ContMDiffWithinAt I J' n g s x) :
    ContMDiffWithinAt I (I'.prod J') n (fun x => (f x, g x)) s x := by
  rw [contMDiffWithinAt_iff] at *
  exact ⟨hf.1.prodMk hg.1, hf.2.prodMk hg.2⟩
/-
**ContMDiffWithinAt.prodMk_space** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffWithinAt.prodMk_space {f : M -> E'} {g : M -> F'} (hf : ContMDiff
WithinAt I 𝓘(𝕜, E') n f s x) (hg : ContMDiffWithinAt I 𝓘(𝕜, F') n g s x) : ContM
DiffWithinAt I 𝓘(𝕜, E' × F') n (fun x => (f x, g x)) s x
参数：hf : ContMDiffWithinAt I 𝓘(𝕜, E') n f s x；hg : ContMDiffWithinAt I 𝓘(𝕜, F') n
 g s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `contMDiffWithinAt_iff`：contMDiffWithinAt_iff : ContMDiffWithinAt I I' n 
f s x ↔ ContinuousWithinAt f s x ∧ ContDiffWithinAt 𝕜 n (extChartAt I' (f x) ∘ f
 ∘ (extChar…
· 使用定理 `ContinuousWithinAt.prodMk`：ContinuousWithinAt.prodMk {f : α -> β} {g : α
 -> γ} {s : Set α} {x : α} (hf : ContinuousWithinAt f s x) (hg : ContinuousWithi
nAt g s x) : Co…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ContDiffWithinAt.prodMk`：ContDiffWithinAt.prodMk {s : Set E} {f : E -> F
} {g : E -> G} (hf : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s 
x) : ContDiff…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem ContMDiffWithinAt.prodMk_space {f : M → E'} {g : M → F'}
    (hf : ContMDiffWithinAt I 𝓘(𝕜, E') n f s x) (hg : ContMDiffWithinAt I 𝓘(𝕜, F') n g s x) :
    ContMDiffWithinAt I 𝓘(𝕜, E' × F') n (fun x => (f x, g x)) s x := by
  rw [contMDiffWithinAt_iff] at *
  exact ⟨hf.1.prodMk hg.1, hf.2.prodMk hg.2⟩

nonrec theorem ContMDiffAt.prodMk {f : M → M'} {g : M → N'} (hf : ContMDiffAt I I' n f x)
    (hg : ContMDiffAt I J' n g x) : ContMDiffAt I (I'.prod J') n (fun x => (f x, g x)) x :=
  hf.prodMk hg

nonrec theorem ContMDiffAt.prodMk_space {f : M → E'} {g : M → F'}
    (hf : ContMDiffAt I 𝓘(𝕜, E') n f x) (hg : ContMDiffAt I 𝓘(𝕜, F') n g x) :
    ContMDiffAt I 𝓘(𝕜, E' × F') n (fun x => (f x, g x)) x :=
  hf.prodMk_space hg
/-
**ContMDiffOn.prodMk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffOn.prodMk {f : M -> M'} {g : M -> N'} (hf : ContMDiffOn I I' n f 
s) (hg : ContMDiffOn I J' n g s) : ContMDiffOn I (I'.prod J') n (fun x => (f x, 
g x)) s
参数：hf : ContMDiffOn I I' n f s；hg : ContMDiffOn I J' n g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffWithinAt.prodMk`：ContMDiffWithinAt.prodMk {f : M -> M'} {g : M 
-> N'} (hf : ContMDiffWithinAt I I' n f s x) (hg : ContMDiffWithinAt I J' n g s 
x) : ContMDiff…
-/
theorem ContMDiffOn.prodMk {f : M → M'} {g : M → N'} (hf : ContMDiffOn I I' n f s)
    (hg : ContMDiffOn I J' n g s) : ContMDiffOn I (I'.prod J') n (fun x => (f x, g x)) s :=
  fun x hx => (hf x hx).prodMk (hg x hx)
/-
**ContMDiffOn.prodMk_space** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffOn.prodMk_space {f : M -> E'} {g : M -> F'} (hf : ContMDiffOn I 𝓘
(𝕜, E') n f s) (hg : ContMDiffOn I 𝓘(𝕜, F') n g s) : ContMDiffOn I 𝓘(𝕜, E' × F')
 n (fun x => (f x, g x)) s
参数：hf : ContMDiffOn I 𝓘(𝕜, E') n f s；hg : ContMDiffOn I 𝓘(𝕜, F') n g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffWithinAt.prodMk_space`：ContMDiffWithinAt.prodMk_space {f : M ->
 E'} {g : M -> F'} (hf : ContMDiffWithinAt I 𝓘(𝕜, E') n f s x) (hg : ContMDiffWi
thinAt I 𝓘(𝕜, F') n …
-/
theorem ContMDiffOn.prodMk_space {f : M → E'} {g : M → F'} (hf : ContMDiffOn I 𝓘(𝕜, E') n f s)
    (hg : ContMDiffOn I 𝓘(𝕜, F') n g s) : ContMDiffOn I 𝓘(𝕜, E' × F') n (fun x => (f x, g x)) s :=
  fun x hx => (hf x hx).prodMk_space (hg x hx)

nonrec theorem ContMDiff.prodMk {f : M → M'} {g : M → N'} (hf : ContMDiff I I' n f)
    (hg : ContMDiff I J' n g) : ContMDiff I (I'.prod J') n fun x => (f x, g x) := fun x =>
  (hf x).prodMk (hg x)
/-
**ContMDiff.prodMk_space** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiff.prodMk_space {f : M -> E'} {g : M -> F'} (hf : ContMDiff I 𝓘(𝕜, 
E') n f) (hg : ContMDiff I 𝓘(𝕜, F') n g) : ContMDiff I 𝓘(𝕜, E' × F') n fun x => 
(f x, g x)
参数：hf : ContMDiff I 𝓘(𝕜, E') n f；hg : ContMDiff I 𝓘(𝕜, F') n g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffAt.prodMk_space`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {H : Type u_…
-/
theorem ContMDiff.prodMk_space {f : M → E'} {g : M → F'} (hf : ContMDiff I 𝓘(𝕜, E') n f)
    (hg : ContMDiff I 𝓘(𝕜, F') n g) : ContMDiff I 𝓘(𝕜, E' × F') n fun x => (f x, g x) := fun x =>
  (hf x).prodMk_space (hg x)

end ProdMk

section Projections

/-
**contMDiffWithinAt_fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffWithinAt_fst {s : Set (M × N)} {p : M × N} : ContMDiffWithinAt (I
.prod J) I n Prod.fst s p
参数：M × N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `contMDiffWithinAt_iff'`：contMDiffWithinAt_iff' : ContMDiffWithinAt I I' 
n f s x ↔ ContinuousWithinAt f s x ∧ ContDiffWithinAt 𝕜 n (extChartAt I' (f x) ∘
 f ∘ (extCha…
· 使用定理 `continuousWithinAt_fst`：continuousWithinAt_fst {s : Set (α × β)} {p : α 
× β} : ContinuousWithinAt Prod.fst s p
· 使用定理 `ContDiffWithinAt.congr`：ContDiffWithinAt.congr (h : ContDiffWithinAt 𝕜 n
 f s x) (h₁ : forall y in s, f₁ y = f y) (hx : f₁ x = f x) : ContDiffWithinAt 𝕜 
n f₁ s x
· 使用定理 `contDiffWithinAt_fst`：contDiffWithinAt_fst {s : Set (E × F)} {p : E × F}
 : ContDiffWithinAt 𝕜 n (Prod.fst : E × F -> E) s p
· 使用定理 `PartialEquiv.right_inv`：right_inv {x : β} (h : x in e.target) : e (e.sym
m x) = x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `PartialEquiv.map_source`：map_source {x : α} (h : x in e.source) : e x in
 e.target
· 使用定理 `mem_extChartAt_source`：mem_extChartAt_source (x : M) : x in (extChartAt 
I x).source
-/
theorem contMDiffWithinAt_fst {s : Set (M × N)} {p : M × N} :
    ContMDiffWithinAt (I.prod J) I n Prod.fst s p := by
  /- porting note: `simp` fails to apply lemmas to `ModelProd`. Was
  rw [contMDiffWithinAt_iff']
  refine' ⟨continuousWithinAt_fst, _⟩
  refine' contDiffWithinAt_fst.congr (fun y hy => _) _
  · simp only [mfld_simps] at hy
    simp only [hy, mfld_simps]
  · simp only [mfld_simps]
  -/
  rw [contMDiffWithinAt_iff']
  refine ⟨continuousWithinAt_fst, contDiffWithinAt_fst.congr (fun y hy => ?_) ?_⟩
  · exact (extChartAt I p.1).right_inv ⟨hy.1.1.1, hy.1.2.1⟩
  · exact (extChartAt I p.1).right_inv <| (extChartAt I p.1).map_source (mem_extChartAt_source _)
/-
**ContMDiffWithinAt.fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffWithinAt.fst {f : N -> M × M'} {s : Set N} {x : N} (hf : ContMDif
fWithinAt J (I.prod I') n f s x) : ContMDiffWithinAt J I n (fun x => (f x).1) s 
x
参数：hf : ContMDiffWithinAt J (I.prod I') n f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffWithinAt.comp`：ContMDiffWithinAt.comp {t : Set M'} {g : M' -> M
''} (x : M) (hg : ContMDiffWithinAt I' I'' n g t (f x)) (hf : ContMDiffWithinAt 
I I' n f s x…
· 使用定理 `contMDiffWithinAt_fst`：contMDiffWithinAt_fst {s : Set (M × N)} {p : M × 
N} : ContMDiffWithinAt (I.prod J) I n Prod.fst s p
· 使用定理 `Set.mapsTo_image`：mapsTo_image (f : α -> β) (s : Set α) : MapsTo f s (f 
'' s)
-/
theorem ContMDiffWithinAt.fst {f : N → M × M'} {s : Set N} {x : N}
    (hf : ContMDiffWithinAt J (I.prod I') n f s x) :
    ContMDiffWithinAt J I n (fun x => (f x).1) s x :=
  contMDiffWithinAt_fst.comp x hf (mapsTo_image f s)
/-
**contMDiffAt_fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffAt_fst {p : M × N} : ContMDiffAt (I.prod J) I n Prod.fst p
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contMDiffWithinAt_fst`：contMDiffWithinAt_fst {s : Set (M × N)} {p : M × 
N} : ContMDiffWithinAt (I.prod J) I n Prod.fst s p
-/
theorem contMDiffAt_fst {p : M × N} : ContMDiffAt (I.prod J) I n Prod.fst p :=
  contMDiffWithinAt_fst
/-
**contMDiffOn_fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffOn_fst {s : Set (M × N)} : ContMDiffOn (I.prod J) I n Prod.fst s
参数：M × N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contMDiffWithinAt_fst`：contMDiffWithinAt_fst {s : Set (M × N)} {p : M × 
N} : ContMDiffWithinAt (I.prod J) I n Prod.fst s p
-/
theorem contMDiffOn_fst {s : Set (M × N)} : ContMDiffOn (I.prod J) I n Prod.fst s := fun _ _ =>
  contMDiffWithinAt_fst
/-
**contMDiff_fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiff_fst : ContMDiff (I.prod J) I n (@Prod.fst M N)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contMDiffAt_fst`：contMDiffAt_fst {p : M × N} : ContMDiffAt (I.prod J) I 
n Prod.fst p
-/
theorem contMDiff_fst : ContMDiff (I.prod J) I n (@Prod.fst M N) := fun _ => contMDiffAt_fst
/-
**ContMDiffAt.fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffAt.fst {f : N -> M × M'} {x : N} (hf : ContMDiffAt J (I.prod I') 
n f x) : ContMDiffAt J I n (fun x => (f x).1) x
参数：hf : ContMDiffAt J (I.prod I') n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffAt.comp`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E
 : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : T
ype u_…
· 使用定理 `contMDiffAt_fst`：contMDiffAt_fst {p : M × N} : ContMDiffAt (I.prod J) I 
n Prod.fst p
-/
theorem ContMDiffAt.fst {f : N → M × M'} {x : N} (hf : ContMDiffAt J (I.prod I') n f x) :
    ContMDiffAt J I n (fun x => (f x).1) x :=
  contMDiffAt_fst.comp x hf
/-
**ContMDiff.fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiff.fst {f : N -> M × M'} (hf : ContMDiff J (I.prod I') n f) : ContM
Diff J I n fun x => (f x).1
参数：hf : ContMDiff J (I.prod I') n f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiff.comp`：ContMDiff.comp {g : M' -> M''} (hg : ContMDiff I' I'' n 
g) (hf : ContMDiff I I' n f) : ContMDiff I I'' n (g ∘ f)
· 使用定理 `contMDiff_fst`：contMDiff_fst : ContMDiff (I.prod J) I n (@Prod.fst M N)
-/
theorem ContMDiff.fst {f : N → M × M'} (hf : ContMDiff J (I.prod I') n f) :
    ContMDiff J I n fun x => (f x).1 :=
  contMDiff_fst.comp hf
/-
**contMDiffWithinAt_snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffWithinAt_snd {s : Set (M × N)} {p : M × N} : ContMDiffWithinAt (I
.prod J) J n Prod.snd s p
参数：M × N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `contMDiffWithinAt_iff'`：contMDiffWithinAt_iff' : ContMDiffWithinAt I I' 
n f s x ↔ ContinuousWithinAt f s x ∧ ContDiffWithinAt 𝕜 n (extChartAt I' (f x) ∘
 f ∘ (extCha…
· 使用定理 `continuousWithinAt_snd`：continuousWithinAt_snd {s : Set (α × β)} {p : α 
× β} : ContinuousWithinAt Prod.snd s p
· 使用定理 `ContDiffWithinAt.congr`：ContDiffWithinAt.congr (h : ContDiffWithinAt 𝕜 n
 f s x) (h₁ : forall y in s, f₁ y = f y) (hx : f₁ x = f x) : ContDiffWithinAt 𝕜 
n f₁ s x
· 使用定理 `contDiffWithinAt_snd`：contDiffWithinAt_snd {s : Set (E × F)} {p : E × F}
 : ContDiffWithinAt 𝕜 n (Prod.snd : E × F -> F) s p
· 使用定理 `PartialEquiv.right_inv`：right_inv {x : β} (h : x in e.target) : e (e.sym
m x) = x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `PartialEquiv.map_source`：map_source {x : α} (h : x in e.source) : e x in
 e.target
· 使用定理 `mem_extChartAt_source`：mem_extChartAt_source (x : M) : x in (extChartAt 
I x).source
-/
theorem contMDiffWithinAt_snd {s : Set (M × N)} {p : M × N} :
    ContMDiffWithinAt (I.prod J) J n Prod.snd s p := by
  /- porting note: `simp` fails to apply lemmas to `ModelProd`. Was
  rw [contMDiffWithinAt_iff']
  refine' ⟨continuousWithinAt_snd, _⟩
  refine' contDiffWithinAt_snd.congr (fun y hy => _) _
  · simp only [mfld_simps] at hy
    simp only [hy, mfld_simps]
  · simp only [mfld_simps]
  -/
  rw [contMDiffWithinAt_iff']
  refine ⟨continuousWithinAt_snd, contDiffWithinAt_snd.congr (fun y hy => ?_) ?_⟩
  · exact (extChartAt J p.2).right_inv ⟨hy.1.1.2, hy.1.2.2⟩
  · exact (extChartAt J p.2).right_inv <| (extChartAt J p.2).map_source (mem_extChartAt_source _)
/-
**ContMDiffWithinAt.snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffWithinAt.snd {f : N -> M × M'} {s : Set N} {x : N} (hf : ContMDif
fWithinAt J (I.prod I') n f s x) : ContMDiffWithinAt J I' n (fun x => (f x).2) s
 x
参数：hf : ContMDiffWithinAt J (I.prod I') n f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffWithinAt.comp`：ContMDiffWithinAt.comp {t : Set M'} {g : M' -> M
''} (x : M) (hg : ContMDiffWithinAt I' I'' n g t (f x)) (hf : ContMDiffWithinAt 
I I' n f s x…
· 使用定理 `contMDiffWithinAt_snd`：contMDiffWithinAt_snd {s : Set (M × N)} {p : M × 
N} : ContMDiffWithinAt (I.prod J) J n Prod.snd s p
· 使用定理 `Set.mapsTo_image`：mapsTo_image (f : α -> β) (s : Set α) : MapsTo f s (f 
'' s)
-/
theorem ContMDiffWithinAt.snd {f : N → M × M'} {s : Set N} {x : N}
    (hf : ContMDiffWithinAt J (I.prod I') n f s x) :
    ContMDiffWithinAt J I' n (fun x => (f x).2) s x :=
  contMDiffWithinAt_snd.comp x hf (mapsTo_image f s)
/-
**contMDiffAt_snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffAt_snd {p : M × N} : ContMDiffAt (I.prod J) J n Prod.snd p
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contMDiffWithinAt_snd`：contMDiffWithinAt_snd {s : Set (M × N)} {p : M × 
N} : ContMDiffWithinAt (I.prod J) J n Prod.snd s p
-/
theorem contMDiffAt_snd {p : M × N} : ContMDiffAt (I.prod J) J n Prod.snd p :=
  contMDiffWithinAt_snd
/-
**contMDiffOn_snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffOn_snd {s : Set (M × N)} : ContMDiffOn (I.prod J) J n Prod.snd s
参数：M × N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contMDiffWithinAt_snd`：contMDiffWithinAt_snd {s : Set (M × N)} {p : M × 
N} : ContMDiffWithinAt (I.prod J) J n Prod.snd s p
-/
theorem contMDiffOn_snd {s : Set (M × N)} : ContMDiffOn (I.prod J) J n Prod.snd s := fun _ _ =>
  contMDiffWithinAt_snd
/-
**contMDiff_snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiff_snd : ContMDiff (I.prod J) J n (@Prod.snd M N)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contMDiffAt_snd`：contMDiffAt_snd {p : M × N} : ContMDiffAt (I.prod J) J 
n Prod.snd p
-/
theorem contMDiff_snd : ContMDiff (I.prod J) J n (@Prod.snd M N) := fun _ => contMDiffAt_snd
/-
**ContMDiffAt.snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffAt.snd {f : N -> M × M'} {x : N} (hf : ContMDiffAt J (I.prod I') 
n f x) : ContMDiffAt J I' n (fun x => (f x).2) x
参数：hf : ContMDiffAt J (I.prod I') n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffAt.comp`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E
 : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : T
ype u_…
· 使用定理 `contMDiffAt_snd`：contMDiffAt_snd {p : M × N} : ContMDiffAt (I.prod J) J 
n Prod.snd p
-/
theorem ContMDiffAt.snd {f : N → M × M'} {x : N} (hf : ContMDiffAt J (I.prod I') n f x) :
    ContMDiffAt J I' n (fun x => (f x).2) x :=
  contMDiffAt_snd.comp x hf
/-
**ContMDiff.snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiff.snd {f : N -> M × M'} (hf : ContMDiff J (I.prod I') n f) : ContM
Diff J I' n fun x => (f x).2
参数：hf : ContMDiff J (I.prod I') n f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiff.comp`：ContMDiff.comp {g : M' -> M''} (hg : ContMDiff I' I'' n 
g) (hf : ContMDiff I I' n f) : ContMDiff I I'' n (g ∘ f)
· 使用定理 `contMDiff_snd`：contMDiff_snd : ContMDiff (I.prod J) J n (@Prod.snd M N)
-/
theorem ContMDiff.snd {f : N → M × M'} (hf : ContMDiff J (I.prod I') n f) :
    ContMDiff J I' n fun x => (f x).2 :=
  contMDiff_snd.comp hf

end Projections

/-
**contMDiffWithinAt_prod_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffWithinAt_prod_iff (f : M -> M' × N') : ContMDiffWithinAt I (I'.pr
od J') n f s x ↔ ContMDiffWithinAt I I' n (Prod.fst ∘ f) s x ∧ ContMDiffWithinAt
 I J' n (Prod.snd ∘ f) s x
参数：f : M -> M' × N'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffWithinAt.fst`：ContMDiffWithinAt.fst {f : N -> M × M'} {s : Set 
N} {x : N} (hf : ContMDiffWithinAt J (I.prod I') n f s x) : ContMDiffWithinAt J 
I n (fun x …
· 使用定理 `ContMDiffWithinAt.snd`：ContMDiffWithinAt.snd {f : N -> M × M'} {s : Set 
N} {x : N} (hf : ContMDiffWithinAt J (I.prod I') n f s x) : ContMDiffWithinAt J 
I' n (fun x…
· 使用定理 `ContMDiffWithinAt.prodMk`：ContMDiffWithinAt.prodMk {f : M -> M'} {g : M 
-> N'} (hf : ContMDiffWithinAt I I' n f s x) (hg : ContMDiffWithinAt I J' n g s 
x) : ContMDiff…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem contMDiffWithinAt_prod_iff (f : M → M' × N') :
    ContMDiffWithinAt I (I'.prod J') n f s x ↔
      ContMDiffWithinAt I I' n (Prod.fst ∘ f) s x ∧ ContMDiffWithinAt I J' n (Prod.snd ∘ f) s x :=
  ⟨fun h => ⟨h.fst, h.snd⟩, fun h => h.1.prodMk h.2⟩
/-
**contMDiffWithinAt_prod_module_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffWithinAt_prod_module_iff (f : M -> F₁ × F₂) : ContMDiffWithinAt I
 𝓘(𝕜, F₁ × F₂) n f s x ↔ ContMDiffWithinAt I 𝓘(𝕜, F₁) n (Prod.fst ∘ f) s x ∧ Con
tMDiffWithinAt I 𝓘(𝕜, F₂) n (Prod.snd ∘ f) s x
参数：f : M -> F₁ × F₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `modelWithCornersSelf_prod`：modelWithCornersSelf_prod : 𝓘(𝕜, E × F) = 𝓘(𝕜
, E).prod 𝓘(𝕜, F)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `chartedSpaceSelf_prod`：chartedSpaceSelf_prod : prodChartedSpace H H H' H
' = chartedSpaceSelf (H × H')
· 使用定理 `contMDiffWithinAt_prod_iff`：contMDiffWithinAt_prod_iff (f : M -> M' × N'
) : ContMDiffWithinAt I (I'.prod J') n f s x ↔ ContMDiffWithinAt I I' n (Prod.fs
t ∘ f) s x ∧ Con…
-/
theorem contMDiffWithinAt_prod_module_iff (f : M → F₁ × F₂) :
    ContMDiffWithinAt I 𝓘(𝕜, F₁ × F₂) n f s x ↔
      ContMDiffWithinAt I 𝓘(𝕜, F₁) n (Prod.fst ∘ f) s x ∧
      ContMDiffWithinAt I 𝓘(𝕜, F₂) n (Prod.snd ∘ f) s x := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact contMDiffWithinAt_prod_iff f
/-
**contMDiffAt_prod_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffAt_prod_iff (f : M -> M' × N') : ContMDiffAt I (I'.prod J') n f x
 ↔ ContMDiffAt I I' n (Prod.fst ∘ f) x ∧ ContMDiffAt I J' n (Prod.snd ∘ f) x
参数：f : M -> M' × N'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `contMDiffWithinAt_prod_iff`：contMDiffWithinAt_prod_iff (f : M -> M' × N'
) : ContMDiffWithinAt I (I'.prod J') n f s x ↔ ContMDiffWithinAt I I' n (Prod.fs
t ∘ f) s x ∧ Con…
-/
theorem contMDiffAt_prod_iff (f : M → M' × N') :
    ContMDiffAt I (I'.prod J') n f x ↔
      ContMDiffAt I I' n (Prod.fst ∘ f) x ∧ ContMDiffAt I J' n (Prod.snd ∘ f) x := by
  simp_rw [← contMDiffWithinAt_univ]; exact contMDiffWithinAt_prod_iff f
/-
**contMDiffAt_prod_module_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffAt_prod_module_iff (f : M -> F₁ × F₂) : ContMDiffAt I 𝓘(𝕜, F₁ × F
₂) n f x ↔ ContMDiffAt I 𝓘(𝕜, F₁) n (Prod.fst ∘ f) x ∧ ContMDiffAt I 𝓘(𝕜, F₂) n 
(Prod.snd ∘ f) x
参数：f : M -> F₁ × F₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `modelWithCornersSelf_prod`：modelWithCornersSelf_prod : 𝓘(𝕜, E × F) = 𝓘(𝕜
, E).prod 𝓘(𝕜, F)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `chartedSpaceSelf_prod`：chartedSpaceSelf_prod : prodChartedSpace H H H' H
' = chartedSpaceSelf (H × H')
· 使用定理 `contMDiffAt_prod_iff`：contMDiffAt_prod_iff (f : M -> M' × N') : ContMDif
fAt I (I'.prod J') n f x ↔ ContMDiffAt I I' n (Prod.fst ∘ f) x ∧ ContMDiffAt I J
' n (Prod.…
-/
theorem contMDiffAt_prod_module_iff (f : M → F₁ × F₂) :
    ContMDiffAt I 𝓘(𝕜, F₁ × F₂) n f x ↔
      ContMDiffAt I 𝓘(𝕜, F₁) n (Prod.fst ∘ f) x ∧ ContMDiffAt I 𝓘(𝕜, F₂) n (Prod.snd ∘ f) x := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact contMDiffAt_prod_iff f
/-
**contMDiffOn_prod_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffOn_prod_iff (f : M -> M' × N') : ContMDiffOn I (I'.prod J') n f s
 ↔ ContMDiffOn I I' n (Prod.fst ∘ f) s ∧ ContMDiffOn I J' n (Prod.snd ∘ f) s
参数：f : M -> M' × N'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `contMDiffWithinAt_prod_iff`：contMDiffWithinAt_prod_iff (f : M -> M' × N'
) : ContMDiffWithinAt I (I'.prod J') n f s x ↔ ContMDiffWithinAt I I' n (Prod.fs
t ∘ f) s x ∧ Con…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem contMDiffOn_prod_iff (f : M → M' × N') :
    ContMDiffOn I (I'.prod J') n f s ↔
      ContMDiffOn I I' n (Prod.fst ∘ f) s ∧ ContMDiffOn I J' n (Prod.snd ∘ f) s :=
  ⟨fun h ↦ ⟨fun x hx ↦ ((contMDiffWithinAt_prod_iff f).1 (h x hx)).1,
      fun x hx ↦ ((contMDiffWithinAt_prod_iff f).1 (h x hx)).2⟩,
    fun h x hx ↦ (contMDiffWithinAt_prod_iff f).2 ⟨h.1 x hx, h.2 x hx⟩⟩
/-
**contMDiffOn_prod_module_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffOn_prod_module_iff (f : M -> F₁ × F₂) : ContMDiffOn I 𝓘(𝕜, F₁ × F
₂) n f s ↔ ContMDiffOn I 𝓘(𝕜, F₁) n (Prod.fst ∘ f) s ∧ ContMDiffOn I 𝓘(𝕜, F₂) n 
(Prod.snd ∘ f) s
参数：f : M -> F₁ × F₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `modelWithCornersSelf_prod`：modelWithCornersSelf_prod : 𝓘(𝕜, E × F) = 𝓘(𝕜
, E).prod 𝓘(𝕜, F)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `chartedSpaceSelf_prod`：chartedSpaceSelf_prod : prodChartedSpace H H H' H
' = chartedSpaceSelf (H × H')
· 使用定理 `contMDiffOn_prod_iff`：contMDiffOn_prod_iff (f : M -> M' × N') : ContMDif
fOn I (I'.prod J') n f s ↔ ContMDiffOn I I' n (Prod.fst ∘ f) s ∧ ContMDiffOn I J
' n (Prod.…
-/
theorem contMDiffOn_prod_module_iff (f : M → F₁ × F₂) :
    ContMDiffOn I 𝓘(𝕜, F₁ × F₂) n f s ↔
      ContMDiffOn I 𝓘(𝕜, F₁) n (Prod.fst ∘ f) s ∧ ContMDiffOn I 𝓘(𝕜, F₂) n (Prod.snd ∘ f) s := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact contMDiffOn_prod_iff f
/-
**contMDiff_prod_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiff_prod_iff (f : M -> M' × N') : ContMDiff I (I'.prod J') n f ↔ Con
tMDiff I I' n (Prod.fst ∘ f) ∧ ContMDiff I J' n (Prod.snd ∘ f)
参数：f : M -> M' × N'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiff.fst`：ContMDiff.fst {f : N -> M × M'} (hf : ContMDiff J (I.prod
 I') n f) : ContMDiff J I n fun x => (f x).1
· 使用定理 `ContMDiff.snd`：ContMDiff.snd {f : N -> M × M'} (hf : ContMDiff J (I.prod
 I') n f) : ContMDiff J I' n fun x => (f x).2
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContMDiff.prodMk`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E
 : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : T
ype u_…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem contMDiff_prod_iff (f : M → M' × N') :
    ContMDiff I (I'.prod J') n f ↔
      ContMDiff I I' n (Prod.fst ∘ f) ∧ ContMDiff I J' n (Prod.snd ∘ f) :=
  ⟨fun h => ⟨h.fst, h.snd⟩, fun h => by convert! h.1.prodMk h.2⟩
/-
**contMDiff_prod_module_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiff_prod_module_iff (f : M -> F₁ × F₂) : ContMDiff I 𝓘(𝕜, F₁ × F₂) n
 f ↔ ContMDiff I 𝓘(𝕜, F₁) n (Prod.fst ∘ f) ∧ ContMDiff I 𝓘(𝕜, F₂) n (Prod.snd ∘ 
f)
参数：f : M -> F₁ × F₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `modelWithCornersSelf_prod`：modelWithCornersSelf_prod : 𝓘(𝕜, E × F) = 𝓘(𝕜
, E).prod 𝓘(𝕜, F)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `chartedSpaceSelf_prod`：chartedSpaceSelf_prod : prodChartedSpace H H H' H
' = chartedSpaceSelf (H × H')
· 使用定理 `contMDiff_prod_iff`：contMDiff_prod_iff (f : M -> M' × N') : ContMDiff I 
(I'.prod J') n f ↔ ContMDiff I I' n (Prod.fst ∘ f) ∧ ContMDiff I J' n (Prod.snd 
∘ f)
-/
theorem contMDiff_prod_module_iff (f : M → F₁ × F₂) :
    ContMDiff I 𝓘(𝕜, F₁ × F₂) n f ↔
      ContMDiff I 𝓘(𝕜, F₁) n (Prod.fst ∘ f) ∧ ContMDiff I 𝓘(𝕜, F₂) n (Prod.snd ∘ f) := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact contMDiff_prod_iff f
/-
**contMDiff_prod_assoc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiff_prod_assoc : ContMDiff ((I.prod I').prod J) (I.prod (I'.prod J))
 n fun x : (M × M') × N => (x.1.1, x.1.2, x.2)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiff.prodMk`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E
 : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : T
ype u_…
· 使用定理 `ContMDiff.fst`：ContMDiff.fst {f : N -> M × M'} (hf : ContMDiff J (I.prod
 I') n f) : ContMDiff J I n fun x => (f x).1
· 使用定理 `contMDiff_fst`：contMDiff_fst : ContMDiff (I.prod J) I n (@Prod.fst M N)
· 使用定理 `ContMDiff.snd`：ContMDiff.snd {f : N -> M × M'} (hf : ContMDiff J (I.prod
 I') n f) : ContMDiff J I' n fun x => (f x).2
· 使用定理 `contMDiff_snd`：contMDiff_snd : ContMDiff (I.prod J) J n (@Prod.snd M N)
-/
theorem contMDiff_prod_assoc :
    ContMDiff ((I.prod I').prod J) (I.prod (I'.prod J)) n
      fun x : (M × M') × N => (x.1.1, x.1.2, x.2) :=
  contMDiff_fst.fst.prodMk <| contMDiff_fst.snd.prodMk contMDiff_snd

/-- `ContMDiffWithinAt.comp` for a function of two arguments. -/
/-
**ContMDiffWithinAt.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffWithinAt.comp {t : Set M'} {g : M' -> M''} (x : M) (hg : ContMDif
fWithinAt I' I'' n g t (f x)) (hf : ContMDiffWithinAt I I' n f s x) (st : MapsTo
 f s t) : ContMDiffWithinAt I I'' n (g ∘ f) s x
参数：x : M；hg : ContMDiffWithinAt I' I'' n g t (f x)；hf : ContMDiffWithinAt I I' n
 f s x；st : MapsTo f s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `contMDiffWithinAt_iff`：contMDiffWithinAt_iff : ContMDiffWithinAt I I' n 
f s x ↔ ContinuousWithinAt f s x ∧ ContDiffWithinAt 𝕜 n (extChartAt I' (f x) ∘ f
 ∘ (extChar…
· 使用定理 `ContinuousWithinAt.comp`：ContinuousWithinAt.comp {g : β -> γ} {t : Set β
} (hg : ContinuousWithinAt g t (f x)) (hf : ContinuousWithinAt f s x) (h : MapsT
o f s t) : Co…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `extChartAt.eq_1`：∀ {𝕜 : Type u_1} {E : Type u_2} {M : Type u_3} {H : Typ
e u_4} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup E] [ins
t_2 :…
· 使用定理 `ModelWithCorners.left_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `inter_mem_nhdsWithin`：inter_mem_nhdsWithin (s : Set α) {t : Set α} {a : 
α} (h : t in 𝓝 a) : s inter t in 𝓝[s] a
· 使用定理 `extChartAt_source_mem_nhds`：extChartAt_source_mem_nhds (x : M) : (extCha
rtAt I x).source in 𝓝 x
· 使用定理 `ContinuousWithinAt.tendsto`：ContinuousWithinAt.tendsto (h : ContinuousWi
thinAt f s x) : Tendsto f (𝓝[s] x) (𝓝 (f x))
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `PartialEquiv.left_inv`：left_inv {x : α} (h : x in e.source) : e.symm (e 
x) = x
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `ContDiffWithinAt.congr_of_eventuallyEq`：ContDiffWithinAt.congr_of_eventu
allyEq (h : ContDiffWithinAt 𝕜 n f s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x)
 : ContDiffWithinAt 𝕜 n f₁ s…
· 使用定理 `ContDiffWithinAt.mono_of_mem_nhdsWithin`：ContDiffWithinAt.mono_of_mem_nh
dsWithin (h : ContDiffWithinAt 𝕜 n f s x) {t : Set E} (hst : s in 𝓝[t] x) : Cont
DiffWithinAt 𝕜 n f t x
· 使用定理 `ContDiffWithinAt.comp`：ContDiffWithinAt.comp {s : Set E} {t : Set F} {g 
: F -> G} {f : E -> F} (x : E) (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : ContD
iffWithinAt…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ContDiffWithinAt.mono`：ContDiffWithinAt.mono (h : ContDiffWithinAt 𝕜 n f
 s x) {t : Set E} (hst : t subseteq s) : ContDiffWithinAt 𝕜 n f t x
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Set.MapsTo.mono_left`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {t
 : Set β} {f : α → β}, Set.MapsTo f s₁ t → s₂ ⊆ s₁ → Set.MapsTo f s₂ t
· 使用定理 `Set.mapsTo_preimage`：mapsTo_preimage (f : α -> β) (t : Set β) : MapsTo f
 (f ⁻¹' t) t
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
`ContMDiffWithinAt.comp` for a function of two arguments.
-/
theorem ContMDiffWithinAt.comp₂ {h : M' × N' → N} {f : M → M'} {g : M → N'} {x : M}
    {t : Set (M' × N')} (ha : ContMDiffWithinAt (I'.prod J') J n h t (f x, g x))
    (fa : ContMDiffWithinAt I I' n f s x) (ga : ContMDiffWithinAt I J' n g s x)
    (st : MapsTo (fun x ↦ (f x, g x)) s t) :
    ContMDiffWithinAt I J n (fun x ↦ h (f x, g x)) s x :=
  ha.comp (f := fun x ↦ (f x, g x)) _ (fa.prodMk ga) st

/-- `ContMDiffWithinAt.comp₂`, with a separate argument for point equality. -/
/-
**ContMDiffWithinAt.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffWithinAt.comp {t : Set M'} {g : M' -> M''} (x : M) (hg : ContMDif
fWithinAt I' I'' n g t (f x)) (hf : ContMDiffWithinAt I I' n f s x) (st : MapsTo
 f s t) : ContMDiffWithinAt I I'' n (g ∘ f) s x
参数：x : M；hg : ContMDiffWithinAt I' I'' n g t (f x)；hf : ContMDiffWithinAt I I' n
 f s x；st : MapsTo f s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `contMDiffWithinAt_iff`：contMDiffWithinAt_iff : ContMDiffWithinAt I I' n 
f s x ↔ ContinuousWithinAt f s x ∧ ContDiffWithinAt 𝕜 n (extChartAt I' (f x) ∘ f
 ∘ (extChar…
· 使用定理 `ContinuousWithinAt.comp`：ContinuousWithinAt.comp {g : β -> γ} {t : Set β
} (hg : ContinuousWithinAt g t (f x)) (hf : ContinuousWithinAt f s x) (h : MapsT
o f s t) : Co…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `extChartAt.eq_1`：∀ {𝕜 : Type u_1} {E : Type u_2} {M : Type u_3} {H : Typ
e u_4} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup E] [ins
t_2 :…
· 使用定理 `ModelWithCorners.left_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `inter_mem_nhdsWithin`：inter_mem_nhdsWithin (s : Set α) {t : Set α} {a : 
α} (h : t in 𝓝 a) : s inter t in 𝓝[s] a
· 使用定理 `extChartAt_source_mem_nhds`：extChartAt_source_mem_nhds (x : M) : (extCha
rtAt I x).source in 𝓝 x
· 使用定理 `ContinuousWithinAt.tendsto`：ContinuousWithinAt.tendsto (h : ContinuousWi
thinAt f s x) : Tendsto f (𝓝[s] x) (𝓝 (f x))
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `PartialEquiv.left_inv`：left_inv {x : α} (h : x in e.source) : e.symm (e 
x) = x
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `ContDiffWithinAt.congr_of_eventuallyEq`：ContDiffWithinAt.congr_of_eventu
allyEq (h : ContDiffWithinAt 𝕜 n f s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x)
 : ContDiffWithinAt 𝕜 n f₁ s…
· 使用定理 `ContDiffWithinAt.mono_of_mem_nhdsWithin`：ContDiffWithinAt.mono_of_mem_nh
dsWithin (h : ContDiffWithinAt 𝕜 n f s x) {t : Set E} (hst : s in 𝓝[t] x) : Cont
DiffWithinAt 𝕜 n f t x
· 使用定理 `ContDiffWithinAt.comp`：ContDiffWithinAt.comp {s : Set E} {t : Set F} {g 
: F -> G} {f : E -> F} (x : E) (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : ContD
iffWithinAt…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ContDiffWithinAt.mono`：ContDiffWithinAt.mono (h : ContDiffWithinAt 𝕜 n f
 s x) {t : Set E} (hst : t subseteq s) : ContDiffWithinAt 𝕜 n f t x
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Set.MapsTo.mono_left`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {t
 : Set β} {f : α → β}, Set.MapsTo f s₁ t → s₂ ⊆ s₁ → Set.MapsTo f s₂ t
· 使用定理 `Set.mapsTo_preimage`：mapsTo_preimage (f : α -> β) (t : Set β) : MapsTo f
 (f ⁻¹' t) t
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
`ContMDiffWithinAt.comp₂`, with a separate argument for point equality.
-/
theorem ContMDiffWithinAt.comp₂_of_eq {h : M' × N' → N} {f : M → M'} {g : M → N'} {x : M}
    {y : M' × N'} {t : Set (M' × N')} (ha : ContMDiffWithinAt (I'.prod J') J n h t y)
    (fa : ContMDiffWithinAt I I' n f s x) (ga : ContMDiffWithinAt I J' n g s x)
    (e : (f x, g x) = y) (st : MapsTo (fun x ↦ (f x, g x)) s t) :
    ContMDiffWithinAt I J n (fun x ↦ h (f x, g x)) s x := by
  rw [← e] at ha
  exact ha.comp₂ fa ga st

/-- `ContMDiffAt.comp` for a function of two arguments. -/
/-
**ContMDiffAt.comp** 是 Mathlib 中的一个定理，位于命名空间 `ContMDiffAt`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_3} [inst_3 : T
opologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type u_4}   [inst_4 : Topol
ogicalSpace M] {E' : Type u_5} [inst_5 : NormedAddCommGroup E'] [inst_6 : Normed
Space 𝕜 E']   {H' : Type u_6} [inst_7 : TopologicalSpace H'] {I' : ModelWithCorn
ers 𝕜 E' H'} {M' : Type u_7}   [inst_8 : TopologicalSpace M'] {E'' : Type u_8} [
inst_9 : NormedAddCommGroup E''] [inst_10 : NormedSpace 𝕜 E'']   {H'' : Type u_9
} [inst_11 : TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''} {M'' : Typ
e u_10}   [inst_12 : TopologicalSpace M''] [inst_13 : ChartedSpace H M] [inst_14
 : ChartedSpace H' M']   [inst_15 : ChartedSpace H'' M''] {f : M → M'} {n : With
Top ℕ∞} {g : M' → M''} (x : M),   ContMDiffAt I' I'' n g (f x) → ContMDiffAt I I
' n f x → ContMDiffAt I I'' n (g ∘ f) x
参数：x : M；f x；g ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffWithinAt.comp`：ContMDiffWithinAt.comp {t : Set M'} {g : M' -> M
''} (x : M) (hg : ContMDiffWithinAt I' I'' n g t (f x)) (hf : ContMDiffWithinAt 
I I' n f s x…
· 使用定理 `Set.mapsTo_univ`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (s : Set α)
, Set.MapsTo f s Set.univ

--- 原说明 ---
`ContMDiffAt.comp` for a function of two arguments.
-/
theorem ContMDiffAt.comp₂ {h : M' × N' → N} {f : M → M'} {g : M → N'} {x : M}
    (ha : ContMDiffAt (I'.prod J') J n h (f x, g x)) (fa : ContMDiffAt I I' n f x)
    (ga : ContMDiffAt I J' n g x) : ContMDiffAt I J n (fun x ↦ h (f x, g x)) x :=
  ha.comp (f := fun x ↦ (f x, g x)) _ (fa.prodMk ga)

/-- `ContMDiffAt.comp₂`, with a separate argument for point equality. -/
/-
**ContMDiffAt.comp** 是 Mathlib 中的一个定理，位于命名空间 `ContMDiffAt`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_3} [inst_3 : T
opologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type u_4}   [inst_4 : Topol
ogicalSpace M] {E' : Type u_5} [inst_5 : NormedAddCommGroup E'] [inst_6 : Normed
Space 𝕜 E']   {H' : Type u_6} [inst_7 : TopologicalSpace H'] {I' : ModelWithCorn
ers 𝕜 E' H'} {M' : Type u_7}   [inst_8 : TopologicalSpace M'] {E'' : Type u_8} [
inst_9 : NormedAddCommGroup E''] [inst_10 : NormedSpace 𝕜 E'']   {H'' : Type u_9
} [inst_11 : TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''} {M'' : Typ
e u_10}   [inst_12 : TopologicalSpace M''] [inst_13 : ChartedSpace H M] [inst_14
 : ChartedSpace H' M']   [inst_15 : ChartedSpace H'' M''] {f : M → M'} {n : With
Top ℕ∞} {g : M' → M''} (x : M),   ContMDiffAt I' I'' n g (f x) → ContMDiffAt I I
' n f x → ContMDiffAt I I'' n (g ∘ f) x
参数：x : M；f x；g ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffWithinAt.comp`：ContMDiffWithinAt.comp {t : Set M'} {g : M' -> M
''} (x : M) (hg : ContMDiffWithinAt I' I'' n g t (f x)) (hf : ContMDiffWithinAt 
I I' n f s x…
· 使用定理 `Set.mapsTo_univ`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (s : Set α)
, Set.MapsTo f s Set.univ

--- 原说明 ---
`ContMDiffAt.comp₂`, with a separate argument for point equality.
-/
theorem ContMDiffAt.comp₂_of_eq {h : M' × N' → N} {f : M → M'} {g : M → N'} {x : M} {y : M' × N'}
    (ha : ContMDiffAt (I'.prod J') J n h y) (fa : ContMDiffAt I I' n f x)
    (ga : ContMDiffAt I J' n g x) (e : (f x, g x) = y) :
    ContMDiffAt I J n (fun x ↦ h (f x, g x)) x := by
  rw [← e] at ha
  exact ha.comp₂ fa ga

/-- Curried `C^n` functions are `C^n` in the first coordinate. -/
/-
**ContMDiffWithinAt.curry_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffWithinAt.curry_left {f : M -> M' -> N} {x : M} {y : M'} {s : Set 
(M × M')} (fa : ContMDiffWithinAt (I.prod I') J n (uncurry f) s (x, y)) : ContMD
iffWithinAt I J n (fun x => f x y) {x | (x, y) in s} x
参数：M × M'；fa : ContMDiffWithinAt (I.prod I') J n (uncurry f) s (x, y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffWithinAt.comp₂`：ContMDiffWithinAt.comp₂ {h : M' × N' -> N} {f :
 M -> M'} {g : M -> N'} {x : M} {t : Set (M' × N')} (ha : ContMDiffWithinAt (I'.
prod J') J n …
· 使用定理 `contMDiffWithinAt_id`：contMDiffWithinAt_id : ContMDiffWithinAt I I n (id
 : M -> M) s x
· 使用定理 `contMDiffWithinAt_const`：contMDiffWithinAt_const : ContMDiffWithinAt I I
' n (fun _ : M => c) s x

--- 原说明 ---
Curried `C^n` functions are `C^n` in the first coordinate.
-/
theorem ContMDiffWithinAt.curry_left {f : M → M' → N} {x : M} {y : M'} {s : Set (M × M')}
    (fa : ContMDiffWithinAt (I.prod I') J n (uncurry f) s (x, y)) :
    ContMDiffWithinAt I J n (fun x ↦ f x y) {x | (x, y) ∈ s} x :=
  fa.comp₂ contMDiffWithinAt_id contMDiffWithinAt_const (fun _ h ↦ h)
alias ContMDiffWithinAt.along_fst := ContMDiffWithinAt.curry_left

/-- Curried `C^n` functions are `C^n` in the second coordinate. -/
/-
**ContMDiffWithinAt.curry_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffWithinAt.curry_right {f : M -> M' -> N} {x : M} {y : M'} {s : Set
 (M × M')} (fa : ContMDiffWithinAt (I.prod I') J n (uncurry f) s (x, y)) : ContM
DiffWithinAt I' J n (fun y => f x y) {y | (x, y) in s} y
参数：M × M'；fa : ContMDiffWithinAt (I.prod I') J n (uncurry f) s (x, y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffWithinAt.comp₂`：ContMDiffWithinAt.comp₂ {h : M' × N' -> N} {f :
 M -> M'} {g : M -> N'} {x : M} {t : Set (M' × N')} (ha : ContMDiffWithinAt (I'.
prod J') J n …
· 使用定理 `contMDiffWithinAt_const`：contMDiffWithinAt_const : ContMDiffWithinAt I I
' n (fun _ : M => c) s x
· 使用定理 `contMDiffWithinAt_id`：contMDiffWithinAt_id : ContMDiffWithinAt I I n (id
 : M -> M) s x

--- 原说明 ---
Curried `C^n` functions are `C^n` in the second coordinate.
-/
theorem ContMDiffWithinAt.curry_right {f : M → M' → N} {x : M} {y : M'} {s : Set (M × M')}
    (fa : ContMDiffWithinAt (I.prod I') J n (uncurry f) s (x, y)) :
    ContMDiffWithinAt I' J n (fun y ↦ f x y) {y | (x, y) ∈ s} y :=
  fa.comp₂ contMDiffWithinAt_const contMDiffWithinAt_id (fun _ h ↦ h)
alias ContMDiffWithinAt.along_snd := ContMDiffWithinAt.curry_right

/-- Curried `C^n` functions are `C^n` in the first coordinate. -/
/-
**ContMDiffAt.curry_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffAt.curry_left {f : M -> M' -> N} {x : M} {y : M'} (fa : ContMDiff
At (I.prod I') J n (uncurry f) (x, y)) : ContMDiffAt I J n (fun x => f x y) x
参数：fa : ContMDiffAt (I.prod I') J n (uncurry f) (x, y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffAt.comp₂`：ContMDiffAt.comp₂ {h : M' × N' -> N} {f : M -> M'} {g
 : M -> N'} {x : M} (ha : ContMDiffAt (I'.prod J') J n h (f x, g x)) (fa : ContM
DiffAt …
· 使用定理 `contMDiffAt_id`：contMDiffAt_id : ContMDiffAt I I n (id : M -> M) x
· 使用定理 `contMDiffAt_const`：contMDiffAt_const : ContMDiffAt I I' n (fun _ : M => 
c) x

--- 原说明 ---
Curried `C^n` functions are `C^n` in the first coordinate.
-/
theorem ContMDiffAt.curry_left {f : M → M' → N} {x : M} {y : M'}
    (fa : ContMDiffAt (I.prod I') J n (uncurry f) (x, y)) :
    ContMDiffAt I J n (fun x ↦ f x y) x :=
  fa.comp₂ contMDiffAt_id contMDiffAt_const
alias ContMDiffAt.along_fst := ContMDiffAt.curry_left

/-- Curried `C^n` functions are `C^n` in the second coordinate. -/
/-
**ContMDiffAt.curry_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffAt.curry_right {f : M -> M' -> N} {x : M} {y : M'} (fa : ContMDif
fAt (I.prod I') J n (uncurry f) (x, y)) : ContMDiffAt I' J n (fun y => f x y) y
参数：fa : ContMDiffAt (I.prod I') J n (uncurry f) (x, y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffAt.comp₂`：ContMDiffAt.comp₂ {h : M' × N' -> N} {f : M -> M'} {g
 : M -> N'} {x : M} (ha : ContMDiffAt (I'.prod J') J n h (f x, g x)) (fa : ContM
DiffAt …
· 使用定理 `contMDiffAt_const`：contMDiffAt_const : ContMDiffAt I I' n (fun _ : M => 
c) x
· 使用定理 `contMDiffAt_id`：contMDiffAt_id : ContMDiffAt I I n (id : M -> M) x

--- 原说明 ---
Curried `C^n` functions are `C^n` in the second coordinate.
-/
theorem ContMDiffAt.curry_right {f : M → M' → N} {x : M} {y : M'}
    (fa : ContMDiffAt (I.prod I') J n (uncurry f) (x, y)) :
    ContMDiffAt I' J n (fun y ↦ f x y) y :=
  fa.comp₂ contMDiffAt_const contMDiffAt_id
alias ContMDiffAt.along_snd := ContMDiffAt.curry_right

/-- Curried `C^n` functions are `C^n` in the first coordinate. -/
/-
**ContMDiffOn.curry_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffOn.curry_left {f : M -> M' -> N} {s : Set (M × M')} (fa : ContMDi
ffOn (I.prod I') J n (uncurry f) s) {y : M'} : ContMDiffOn I J n (fun x => f x y
) {x | (x, y) in s}
参数：M × M'；fa : ContMDiffOn (I.prod I') J n (uncurry f) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffWithinAt.along_fst`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormed
Field 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 
𝕜 E] {H : Type u_…

--- 原说明 ---
Curried `C^n` functions are `C^n` in the first coordinate.
-/
theorem ContMDiffOn.curry_left {f : M → M' → N} {s : Set (M × M')}
    (fa : ContMDiffOn (I.prod I') J n (uncurry f) s) {y : M'} :
    ContMDiffOn I J n (fun x ↦ f x y) {x | (x, y) ∈ s} :=
  fun x m ↦ (fa (x, y) m).along_fst
alias ContMDiffOn.along_fst := ContMDiffOn.curry_left

/-- Curried `C^n` functions are `C^n` in the second coordinate. -/
/-
**ContMDiffOn.curry_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffOn.curry_right {f : M -> M' -> N} {x : M} {s : Set (M × M')} (fa 
: ContMDiffOn (I.prod I') J n (uncurry f) s) : ContMDiffOn I' J n (fun y => f x 
y) {y | (x, y) in s}
参数：M × M'；fa : ContMDiffOn (I.prod I') J n (uncurry f) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffWithinAt.along_snd`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormed
Field 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 
𝕜 E] {H : Type u_…

--- 原说明 ---
Curried `C^n` functions are `C^n` in the second coordinate.
-/
theorem ContMDiffOn.curry_right {f : M → M' → N} {x : M} {s : Set (M × M')}
    (fa : ContMDiffOn (I.prod I') J n (uncurry f) s) :
    ContMDiffOn I' J n (fun y ↦ f x y) {y | (x, y) ∈ s} :=
  fun y m ↦ (fa (x, y) m).along_snd
alias ContMDiffOn.along_snd := ContMDiffOn.curry_right

/-- Curried `C^n` functions are `C^n` in the first coordinate. -/
/-
**ContMDiff.curry_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiff.curry_left {f : M -> M' -> N} (fa : ContMDiff (I.prod I') J n (u
ncurry f)) {y : M'} : ContMDiff I J n (fun x => f x y)
参数：fa : ContMDiff (I.prod I') J n (uncurry f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffAt.along_fst`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
H : Type u_…

--- 原说明 ---
Curried `C^n` functions are `C^n` in the first coordinate.
-/
theorem ContMDiff.curry_left {f : M → M' → N}
    (fa : ContMDiff (I.prod I') J n (uncurry f)) {y : M'} :
    ContMDiff I J n (fun x ↦ f x y) :=
  fun _ ↦ (fa _).along_fst
alias ContMDiff.along_fst := ContMDiff.curry_left

/-- Curried `C^n` functions are `C^n` in the second coordinate. -/
/-
**ContMDiff.curry_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiff.curry_right {f : M -> M' -> N} {x : M} (fa : ContMDiff (I.prod I
') J n (uncurry f)) : ContMDiff I' J n (fun y => f x y)
参数：fa : ContMDiff (I.prod I') J n (uncurry f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffAt.along_snd`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
H : Type u_…

--- 原说明 ---
Curried `C^n` functions are `C^n` in the second coordinate.
-/
theorem ContMDiff.curry_right {f : M → M' → N} {x : M}
    (fa : ContMDiff (I.prod I') J n (uncurry f)) :
    ContMDiff I' J n (fun y ↦ f x y) :=
  fun _ ↦ (fa _).along_snd
alias ContMDiff.along_snd := ContMDiff.curry_right

section prodMap

variable {g : N → N'} {r : Set N} {y : N}

/-- The product map of two `C^n` functions within a set at a point is `C^n`
within the product set at the product point. -/
/-
**ContMDiffWithinAt.prodMap'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffWithinAt.prodMap' {p : M × N} (hf : ContMDiffWithinAt I I' n f s 
p.1) (hg : ContMDiffWithinAt J J' n g r p.2) : ContMDiffWithinAt (I.prod J) (I'.
prod J') n (Prod.map f g) (s ×ˢ r) p
参数：hf : ContMDiffWithinAt I I' n f s p.1；hg : ContMDiffWithinAt J J' n g r p.2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffWithinAt.prodMk`：ContMDiffWithinAt.prodMk {f : M -> M'} {g : M 
-> N'} (hf : ContMDiffWithinAt I I' n f s x) (hg : ContMDiffWithinAt I J' n g s 
x) : ContMDiff…
· 使用定理 `ContMDiffWithinAt.comp`：ContMDiffWithinAt.comp {t : Set M'} {g : M' -> M
''} (x : M) (hg : ContMDiffWithinAt I' I'' n g t (f x)) (hf : ContMDiffWithinAt 
I I' n f s x…
· 使用定理 `contMDiffWithinAt_fst`：contMDiffWithinAt_fst {s : Set (M × N)} {p : M × 
N} : ContMDiffWithinAt (I.prod J) I n Prod.fst s p
· 使用引理 `Set.mapsTo_fst_prod`：mapsTo_fst_prod {s : Set α} {t : Set β} : MapsTo Pr
od.fst (s ×ˢ t) s
· 使用定理 `contMDiffWithinAt_snd`：contMDiffWithinAt_snd {s : Set (M × N)} {p : M × 
N} : ContMDiffWithinAt (I.prod J) J n Prod.snd s p
· 使用引理 `Set.mapsTo_snd_prod`：mapsTo_snd_prod {s : Set α} {t : Set β} : MapsTo Pr
od.snd (s ×ˢ t) t

--- 原说明 ---
The product map of two `C^n` functions within a set at a point is `C^n`
within the product set at the product point.
-/
theorem ContMDiffWithinAt.prodMap' {p : M × N} (hf : ContMDiffWithinAt I I' n f s p.1)
    (hg : ContMDiffWithinAt J J' n g r p.2) :
    ContMDiffWithinAt (I.prod J) (I'.prod J') n (Prod.map f g) (s ×ˢ r) p :=
  (hf.comp p contMDiffWithinAt_fst mapsTo_fst_prod).prodMk <|
    hg.comp p contMDiffWithinAt_snd mapsTo_snd_prod
/-
**ContMDiffWithinAt.prodMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffWithinAt.prodMap (hf : ContMDiffWithinAt I I' n f s x) (hg : Cont
MDiffWithinAt J J' n g r y) : ContMDiffWithinAt (I.prod J) (I'.prod J') n (Prod.
map f g) (s ×ˢ r) (x, y)
参数：hf : ContMDiffWithinAt I I' n f s x；hg : ContMDiffWithinAt J J' n g r y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffWithinAt.prodMap'`：ContMDiffWithinAt.prodMap' {p : M × N} (hf :
 ContMDiffWithinAt I I' n f s p.1) (hg : ContMDiffWithinAt J J' n g r p.2) : Con
tMDiffWithinAt (…
-/
theorem ContMDiffWithinAt.prodMap (hf : ContMDiffWithinAt I I' n f s x)
    (hg : ContMDiffWithinAt J J' n g r y) :
    ContMDiffWithinAt (I.prod J) (I'.prod J') n (Prod.map f g) (s ×ˢ r) (x, y) :=
  ContMDiffWithinAt.prodMap' hf hg
/-
**ContMDiffAt.prodMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffAt.prodMap (hf : ContMDiffAt I I' n f x) (hg : ContMDiffAt J J' n
 g y) : ContMDiffAt (I.prod J) (I'.prod J') n (Prod.map f g) (x, y)
参数：hf : ContMDiffAt I I' n f x；hg : ContMDiffAt J J' n g y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContMDiffWithinAt.prodMap`：ContMDiffWithinAt.prodMap (hf : ContMDiffWith
inAt I I' n f s x) (hg : ContMDiffWithinAt J J' n g r y) : ContMDiffWithinAt (I.
prod J) (I'.pro…
-/
theorem ContMDiffAt.prodMap (hf : ContMDiffAt I I' n f x) (hg : ContMDiffAt J J' n g y) :
    ContMDiffAt (I.prod J) (I'.prod J') n (Prod.map f g) (x, y) := by
  simp only [← contMDiffWithinAt_univ, ← univ_prod_univ] at *
  exact hf.prodMap hg
/-
**ContMDiffAt.prodMap'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffAt.prodMap' {p : M × N} (hf : ContMDiffAt I I' n f p.1) (hg : Con
tMDiffAt J J' n g p.2) : ContMDiffAt (I.prod J) (I'.prod J') n (Prod.map f g) p
参数：hf : ContMDiffAt I I' n f p.1；hg : ContMDiffAt J J' n g p.2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffAt.prodMap`：ContMDiffAt.prodMap (hf : ContMDiffAt I I' n f x) (
hg : ContMDiffAt J J' n g y) : ContMDiffAt (I.prod J) (I'.prod J') n (Prod.map f
 g) (x, y…
-/
theorem ContMDiffAt.prodMap' {p : M × N} (hf : ContMDiffAt I I' n f p.1)
    (hg : ContMDiffAt J J' n g p.2) : ContMDiffAt (I.prod J) (I'.prod J') n (Prod.map f g) p :=
  hf.prodMap hg
/-
**ContMDiffOn.prodMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffOn.prodMap (hf : ContMDiffOn I I' n f s) (hg : ContMDiffOn J J' n
 g r) : ContMDiffOn (I.prod J) (I'.prod J') n (Prod.map f g) (s ×ˢ r)
参数：hf : ContMDiffOn I I' n f s；hg : ContMDiffOn J J' n g r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffOn.prodMk`：ContMDiffOn.prodMk {f : M -> M'} {g : M -> N'} (hf :
 ContMDiffOn I I' n f s) (hg : ContMDiffOn I J' n g s) : ContMDiffOn I (I'.prod 
J') n (f…
· 使用定理 `ContMDiffOn.comp`：ContMDiffOn.comp {t : Set M'} {g : M' -> M''} (hg : Co
ntMDiffOn I' I'' n g t) (hf : ContMDiffOn I I' n f s) (st : s subseteq f ⁻¹' t) 
: Cont…
· 使用定理 `contMDiffOn_fst`：contMDiffOn_fst {s : Set (M × N)} : ContMDiffOn (I.prod
 J) I n Prod.fst s
· 使用引理 `Set.mapsTo_fst_prod`：mapsTo_fst_prod {s : Set α} {t : Set β} : MapsTo Pr
od.fst (s ×ˢ t) s
· 使用定理 `contMDiffOn_snd`：contMDiffOn_snd {s : Set (M × N)} : ContMDiffOn (I.prod
 J) J n Prod.snd s
· 使用引理 `Set.mapsTo_snd_prod`：mapsTo_snd_prod {s : Set α} {t : Set β} : MapsTo Pr
od.snd (s ×ˢ t) t
-/
theorem ContMDiffOn.prodMap (hf : ContMDiffOn I I' n f s) (hg : ContMDiffOn J J' n g r) :
    ContMDiffOn (I.prod J) (I'.prod J') n (Prod.map f g) (s ×ˢ r) :=
  (hf.comp contMDiffOn_fst mapsTo_fst_prod).prodMk <| hg.comp contMDiffOn_snd mapsTo_snd_prod
/-
**ContMDiff.prodMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiff.prodMap (hf : ContMDiff I I' n f) (hg : ContMDiff J J' n g) : Co
ntMDiff (I.prod J) (I'.prod J') n (Prod.map f g)
参数：hf : ContMDiff I I' n f；hg : ContMDiff J J' n g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffAt.prodMap'`：ContMDiffAt.prodMap' {p : M × N} (hf : ContMDiffAt
 I I' n f p.1) (hg : ContMDiffAt J J' n g p.2) : ContMDiffAt (I.prod J) (I'.prod
 J') n (Pr…
-/
theorem ContMDiff.prodMap (hf : ContMDiff I I' n f) (hg : ContMDiff J J' n g) :
    ContMDiff (I.prod J) (I'.prod J') n (Prod.map f g) := by
  intro p
  exact (hf p.1).prodMap' (hg p.2)

end prodMap

section PiSpace

/-!
### Regularity of functions with codomain `Π i, F i`

We have no `ModelWithCorners.pi` yet, so we prove lemmas about functions `f : M → Π i, F i` and
use `𝓘(𝕜, Π i, F i)` as the model space.
-/


variable {ι : Type*} [Fintype ι] {Fi : ι → Type*} [∀ i, NormedAddCommGroup (Fi i)]
  [∀ i, NormedSpace 𝕜 (Fi i)] {φ : M → ∀ i, Fi i}

/-
**contMDiffWithinAt_pi_space** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffWithinAt_pi_space : ContMDiffWithinAt I 𝓘(𝕜, forall i, Fi i) n φ 
s x ↔ forall i, ContMDiffWithinAt I 𝓘(𝕜, Fi i) n (fun x => φ x i) s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `extChartAt_model_space_eq_id`：extChartAt_model_space_eq_id (x : E) : ext
ChartAt 𝓘(𝕜, E) x = PartialEquiv.refl E
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem contMDiffWithinAt_pi_space :
    ContMDiffWithinAt I 𝓘(𝕜, ∀ i, Fi i) n φ s x ↔
      ∀ i, ContMDiffWithinAt I 𝓘(𝕜, Fi i) n (fun x => φ x i) s x := by
  simp only [contMDiffWithinAt_iff, continuousWithinAt_pi, contDiffWithinAt_pi, forall_and,
    extChartAt_model_space_eq_id, Function.comp_def, PartialEquiv.refl_coe, id]
/-
**contMDiffOn_pi_space** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffOn_pi_space : ContMDiffOn I 𝓘(𝕜, forall i, Fi i) n φ s ↔ forall i
, ContMDiffOn I 𝓘(𝕜, Fi i) n (fun x => φ x i) s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `contMDiffWithinAt_pi_space`：contMDiffWithinAt_pi_space : ContMDiffWithin
At I 𝓘(𝕜, forall i, Fi i) n φ s x ↔ forall i, ContMDiffWithinAt I 𝓘(𝕜, Fi i) n (
fun x => φ x i) …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem contMDiffOn_pi_space :
    ContMDiffOn I 𝓘(𝕜, ∀ i, Fi i) n φ s ↔ ∀ i, ContMDiffOn I 𝓘(𝕜, Fi i) n (fun x => φ x i) s :=
  ⟨fun h i x hx => contMDiffWithinAt_pi_space.1 (h x hx) i, fun h x hx =>
    contMDiffWithinAt_pi_space.2 fun i => h i x hx⟩
/-
**contMDiffAt_pi_space** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffAt_pi_space : ContMDiffAt I 𝓘(𝕜, forall i, Fi i) n φ x ↔ forall i
, ContMDiffAt I 𝓘(𝕜, Fi i) n (fun x => φ x i) x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contMDiffWithinAt_pi_space`：contMDiffWithinAt_pi_space : ContMDiffWithin
At I 𝓘(𝕜, forall i, Fi i) n φ s x ↔ forall i, ContMDiffWithinAt I 𝓘(𝕜, Fi i) n (
fun x => φ x i) …
-/
theorem contMDiffAt_pi_space :
    ContMDiffAt I 𝓘(𝕜, ∀ i, Fi i) n φ x ↔ ∀ i, ContMDiffAt I 𝓘(𝕜, Fi i) n (fun x => φ x i) x :=
  contMDiffWithinAt_pi_space
/-
**contMDiff_pi_space** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiff_pi_space : ContMDiff I 𝓘(𝕜, forall i, Fi i) n φ ↔ forall i, Cont
MDiff I 𝓘(𝕜, Fi i) n fun x => φ x i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `contMDiffAt_pi_space`：contMDiffAt_pi_space : ContMDiffAt I 𝓘(𝕜, forall i
, Fi i) n φ x ↔ forall i, ContMDiffAt I 𝓘(𝕜, Fi i) n (fun x => φ x i) x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem contMDiff_pi_space :
    ContMDiff I 𝓘(𝕜, ∀ i, Fi i) n φ ↔ ∀ i, ContMDiff I 𝓘(𝕜, Fi i) n fun x => φ x i :=
  ⟨fun h i x => contMDiffAt_pi_space.1 (h x) i, fun h x => contMDiffAt_pi_space.2 fun i => h i x⟩

end PiSpace

section disjointUnion

variable {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M'] {n : WithTop ℕ∞}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {J : Type*} {J : ModelWithCorners 𝕜 E' H'}
  {N N' : Type*} [TopologicalSpace N] [TopologicalSpace N'] [ChartedSpace H' N] [ChartedSpace H' N']

open Topology

/-
**ContMDiff.inl** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContMDiff.inl : ContMDiff I I n (@Sum.inl M M')
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `contMDiffAt_iff`：contMDiffAt_iff {n : Nat∞ω} {f : M -> M'} {x : M} : Con
tMDiffAt I I' n f x ↔ ContinuousAt f x ∧ ContDiffWithinAt 𝕜 n (extChartAt I' (f 
x) ∘ …
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `continuous_inl`：continuous_inl : Continuous (@inl X Y)
· 使用定理 `ContDiffWithinAt.congr_of_eventuallyEq`：ContDiffWithinAt.congr_of_eventu
allyEq (h : ContDiffWithinAt 𝕜 n f s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x)
 : ContDiffWithinAt 𝕜 n f₁ s…
· 使用定理 `contDiffWithinAt_id`：contDiffWithinAt_id {s x} : ContDiffWithinAt 𝕜 n (i
d : E -> E) s x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ModelWithCorners.image_eq`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用引理 `OpenPartialHomeomorph.extend_image_target_mem_nhds`：extend_image_target_
mem_nhds {x : M} (hx : x in f.source) : I '' f.target in 𝓝[range I] (f.extend I)
 x
· 使用引理 `mem_chart_source`：mem_chart_source (H : Type*) {M : Type*} [TopologicalS
pace H] [TopologicalSpace M] [ChartedSpace H M] (x : M) : x in (chartAt H x).sou
rce
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `nonempty_of_chartedSpace`：nonempty_of_chartedSpace {H : Type*} {M : Type
*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] (x : M) : Nonemp
ty H
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Topology.IsOpenEmbedding.inl`：∀ {X : Type u} {Y : Type v} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y], Topology.IsOpenEmbedding Sum.inl
· 使用引理 `ChartedSpace.sum_chartAt_inl`：ChartedSpace.sum_chartAt_inl (x : M) : hav
eI : Nonempty H
· 使用定理 `OpenPartialHomeomorph.lift_openEmbedding.congr_simp`：∀ {X : Type u_7} {X
' : Type u_8} {Z : Type u_9} [inst : TopologicalSpace X] [inst_1 : TopologicalSp
ace X']   [inst_2 : TopologicalSpace Z] […
· 使用定理 `Function.Injective.extend_apply`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Injective f → ∀ (g : α → γ) (e' : β → γ) (a : α)
, Function.extend f g…
· 使用定理 `Sum.inl_injective`：inl_injective : Function.Injective (inl : α -> α oplu
s β)
· 使用定理 `OpenPartialHomeomorph.right_inv`：right_inv {x : Y} (h : x in e.target) :
 e (e.symm x) = x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ModelWithCorners.right_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ModelWithCorners.left_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x
-/
lemma ContMDiff.inl : ContMDiff I I n (@Sum.inl M M') := by
  intro x
  rw [contMDiffAt_iff]
  refine ⟨continuous_inl.continuousAt, ?_⟩
  -- In extended charts, .inl equals the identity (on the chart sources).
  apply contDiffWithinAt_id.congr_of_eventuallyEq; swap
  · simp [ChartedSpace.sum_chartAt_inl, Sum.inl_injective.extend_apply (chartAt _ x)]
  set C := chartAt H x with hC
  have : I.symm ⁻¹' C.target ∩ range I ∈ 𝓝[range I] (extChartAt I x) x := by
    rw [← I.image_eq (chartAt H x).target]
    exact (chartAt H x).extend_image_target_mem_nhds (mem_chart_source _ x)
  filter_upwards [this] with y hy
  simp [extChartAt, sum_chartAt_inl, ← hC, Sum.inl_injective.extend_apply C, C.right_inv hy.1,
    I.right_inv hy.2]
/-
**ContMDiff.inr** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContMDiff.inr : ContMDiff I I n (@Sum.inr M M')
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `contMDiffAt_iff`：contMDiffAt_iff {n : Nat∞ω} {f : M -> M'} {x : M} : Con
tMDiffAt I I' n f x ↔ ContinuousAt f x ∧ ContDiffWithinAt 𝕜 n (extChartAt I' (f 
x) ∘ …
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `continuous_inr`：continuous_inr : Continuous (@inr X Y)
· 使用定理 `ContDiffWithinAt.congr_of_eventuallyEq`：ContDiffWithinAt.congr_of_eventu
allyEq (h : ContDiffWithinAt 𝕜 n f s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x)
 : ContDiffWithinAt 𝕜 n f₁ s…
· 使用定理 `contDiffWithinAt_id`：contDiffWithinAt_id {s x} : ContDiffWithinAt 𝕜 n (i
d : E -> E) s x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ModelWithCorners.image_eq`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用引理 `OpenPartialHomeomorph.extend_image_target_mem_nhds`：extend_image_target_
mem_nhds {x : M} (hx : x in f.source) : I '' f.target in 𝓝[range I] (f.extend I)
 x
· 使用引理 `mem_chart_source`：mem_chart_source (H : Type*) {M : Type*} [TopologicalS
pace H] [TopologicalSpace M] [ChartedSpace H M] (x : M) : x in (chartAt H x).sou
rce
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `nonempty_of_chartedSpace`：nonempty_of_chartedSpace {H : Type*} {M : Type
*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] (x : M) : Nonemp
ty H
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Topology.IsOpenEmbedding.inr`：∀ {X : Type u} {Y : Type v} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y], Topology.IsOpenEmbedding Sum.inr
· 使用引理 `ChartedSpace.sum_chartAt_inr`：ChartedSpace.sum_chartAt_inr (x' : M') : h
aveI : Nonempty H
· 使用定理 `OpenPartialHomeomorph.lift_openEmbedding.congr_simp`：∀ {X : Type u_7} {X
' : Type u_8} {Z : Type u_9} [inst : TopologicalSpace X] [inst_1 : TopologicalSp
ace X']   [inst_2 : TopologicalSpace Z] […
· 使用定理 `Function.Injective.extend_apply`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Injective f → ∀ (g : α → γ) (e' : β → γ) (a : α)
, Function.extend f g…
· 使用定理 `Sum.inr_injective`：inr_injective : Function.Injective (inr : β -> α oplu
s β)
· 使用定理 `OpenPartialHomeomorph.right_inv`：right_inv {x : Y} (h : x in e.target) :
 e (e.symm x) = x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ModelWithCorners.right_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ModelWithCorners.left_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x
-/
lemma ContMDiff.inr : ContMDiff I I n (@Sum.inr M M') := by
  intro x
  rw [contMDiffAt_iff]
  refine ⟨continuous_inr.continuousAt, ?_⟩
  -- In extended charts, .inl equals the identity (on the chart sources).
  apply contDiffWithinAt_id.congr_of_eventuallyEq; swap
  · simp only [mfld_simps, sum_chartAt_inr]
    congr
    apply Sum.inr_injective.extend_apply (chartAt _ x)
  set C := chartAt H x with hC
  have : I.symm ⁻¹' (chartAt H x).target ∩ range I ∈ 𝓝[range I] (extChartAt I x) x := by
    rw [← I.image_eq (chartAt H x).target]
    exact (chartAt H x).extend_image_target_mem_nhds (mem_chart_source _ x)
  filter_upwards [this] with y hy
  simp [extChartAt, sum_chartAt_inr, ← hC, Sum.inr_injective.extend_apply C, C.right_inv hy.1,
    I.right_inv hy.2]
/-
**extChartAt_inl_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：extChartAt_inl_apply {x y : M} : (extChartAt I (.inl x : M oplus M')) (Sum
.inl y) = (extChartAt I x) y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sum_chartAt_inl_apply`：∀ {H : Type u} {M : Type u_2} {M' : Type u_3} [in
st : TopologicalSpace H] [inst_1 : TopologicalSpace M]   [inst_2 : TopologicalSp
ace M'] [cm…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma extChartAt_inl_apply {x y : M} :
    (extChartAt I (.inl x : M ⊕ M')) (Sum.inl y) = (extChartAt I x) y := by simp
/-
**extChartAt_inr_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：extChartAt_inr_apply {x y : M'} : (extChartAt I (.inr x : M oplus M')) (Su
m.inr y) = (extChartAt I x) y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sum_chartAt_inr_apply`：∀ {H : Type u} {M : Type u_2} {M' : Type u_3} [in
st : TopologicalSpace H] [inst_1 : TopologicalSpace M]   [inst_2 : TopologicalSp
ace M'] [cm…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma extChartAt_inr_apply {x y : M'} :
    (extChartAt I (.inr x : M ⊕ M')) (Sum.inr y) = (extChartAt I x) y := by simp
/-
**ContMDiff.sumElim** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContMDiff.sumElim {f : M -> N} {g : M' -> N} (hf : ContMDiff I J n f) (hg 
: ContMDiff I J n g) : ContMDiff I J n (Sum.elim f g)
参数：hf : ContMDiff I J n f；hg : ContMDiff I J n g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `contMDiffAt_iff`：contMDiffAt_iff {n : Nat∞ω} {f : M -> M'} {x : M} : Con
tMDiffAt I I' n f x ↔ ContinuousAt f x ∧ ContDiffWithinAt 𝕜 n (extChartAt I' (f 
x) ∘ …
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `Continuous.sumElim`：Continuous.sumElim {f : X -> Z} {g : Y -> Z} (hf : C
ontinuous f) (hg : Continuous g) : Continuous (Sum.elim f g)
· 使用定理 `ContMDiff.continuous`：ContMDiff.continuous (hf : ContMDiff I I' n f) : C
ontinuous f
· 使用定理 `sum_chartAt_inl_apply`：∀ {H : Type u} {M : Type u_2} {M' : Type u_3} [in
st : TopologicalSpace H] [inst_1 : TopologicalSpace M]   [inst_2 : TopologicalSp
ace M'] [cm…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ContDiffWithinAt.congr_of_eventuallyEq`：ContDiffWithinAt.congr_of_eventu
allyEq (h : ContDiffWithinAt 𝕜 n f s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x)
 : ContDiffWithinAt 𝕜 n f₁ s…
· 使用引理 `nonempty_of_chartedSpace`：nonempty_of_chartedSpace {H : Type*} {M : Type
*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] (x : M) : Nonemp
ty H
· 使用定理 `Topology.IsOpenEmbedding.inl`：∀ {X : Type u} {Y : Type v} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y], Topology.IsOpenEmbedding Sum.inl
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `ChartedSpace.sum_chartAt_inl`：ChartedSpace.sum_chartAt_inl (x : M) : hav
eI : Nonempty H
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sum_chartAt_inr_apply`：∀ {H : Type u} {M : Type u_2} {M' : Type u_3} [in
st : TopologicalSpace H] [inst_1 : TopologicalSpace M]   [inst_2 : TopologicalSp
ace M'] [cm…
· 使用定理 `Topology.IsOpenEmbedding.inr`：∀ {X : Type u} {Y : Type v} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y], Topology.IsOpenEmbedding Sum.inr
· 使用引理 `ChartedSpace.sum_chartAt_inr`：ChartedSpace.sum_chartAt_inr (x' : M') : h
aveI : Nonempty H
-/
lemma ContMDiff.sumElim {f : M → N} {g : M' → N}
    (hf : ContMDiff I J n f) (hg : ContMDiff I J n g) : ContMDiff I J n (Sum.elim f g) := by
  intro p
  rw [contMDiffAt_iff]
  refine ⟨(Continuous.sumElim hf.continuous hg.continuous).continuousAt, ?_⟩
  cases p with
  | inl x =>
    -- In charts around x : M, the map f ⊔ g looks like f.
    -- This is how they both look like in extended charts.
    have : ContDiffWithinAt 𝕜 n ((extChartAt J (f x)) ∘ f ∘ (extChartAt I x).symm)
        (range I) ((extChartAt I (.inl x : M ⊕ M')) (Sum.inl x)) := by
      let hf' := hf x
      rw [contMDiffAt_iff] at hf'
      simpa using hf'.2
    apply this.congr_of_eventuallyEq
    · simp only [extChartAt, Sum.elim_inl, ChartedSpace.sum_chartAt_inl]
      filter_upwards with a
      congr
    · -- They agree at the image of x.
      simp only [extChartAt, ChartedSpace.sum_chartAt_inl, Sum.elim_inl]
      congr
  | inr x =>
    -- In charts around x : M, the map f ⊔ g looks like g.
    -- This is how they both look like in extended charts.
    have : ContDiffWithinAt 𝕜 n ((extChartAt J (g x)) ∘ g ∘ (extChartAt I x).symm)
        (range I) ((extChartAt I (.inr x : M ⊕ M')) (Sum.inr x)) := by
      let hg' := hg x
      rw [contMDiffAt_iff] at hg'
      simpa using hg'.2
    apply this.congr_of_eventuallyEq
    · simp only [extChartAt, Sum.elim_inr, ChartedSpace.sum_chartAt_inr]
      filter_upwards with a
      congr
    · -- They agree at the image of x.
      simp only [extChartAt, ChartedSpace.sum_chartAt_inr, Sum.elim_inr]
      congr
/-
**ContMDiff.sumMap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContMDiff.sumMap {f : M -> N} {g : M' -> N'} (hf : ContMDiff I J n f) (hg 
: ContMDiff I J n g) : ContMDiff I J n (Sum.map f g)
参数：hf : ContMDiff I J n f；hg : ContMDiff I J n g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContMDiff.sumElim`：ContMDiff.sumElim {f : M -> N} {g : M' -> N} (hf : Co
ntMDiff I J n f) (hg : ContMDiff I J n g) : ContMDiff I J n (Sum.elim f g)
· 使用定理 `ContMDiff.comp`：ContMDiff.comp {g : M' -> M''} (hg : ContMDiff I' I'' n 
g) (hf : ContMDiff I I' n f) : ContMDiff I I'' n (g ∘ f)
· 使用引理 `ContMDiff.inl`：ContMDiff.inl : ContMDiff I I n (@Sum.inl M M')
· 使用引理 `ContMDiff.inr`：ContMDiff.inr : ContMDiff I I n (@Sum.inr M M')
-/
lemma ContMDiff.sumMap {f : M → N} {g : M' → N'}
    (hf : ContMDiff I J n f) (hg : ContMDiff I J n g) : ContMDiff I J n (Sum.map f g) :=
  ContMDiff.sumElim (ContMDiff.inl.comp hf) (ContMDiff.inr.comp hg)
/-
**contMDiff_of_contMDiff_inl** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：contMDiff_of_contMDiff_inl {f : M -> N} (h : ContMDiff I J n ((@Sum.inl N 
N') ∘ f)) : ContMDiff I J n f
参数：h : ContMDiff I J n ((@Sum.inl N N') ∘ f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `contMDiffOn_univ`：contMDiffOn_univ : ContMDiffOn I I' n f univ ↔ ContMDi
ff I I' n f
· 使用定理 `ContMDiffOn.comp`：ContMDiffOn.comp {t : Set M'} {g : M' -> M''} (hg : Co
ntMDiffOn I' I'' n g t) (hf : ContMDiffOn I I' n f s) (st : s subseteq f ⁻¹' t) 
: Cont…
· 使用定理 `ContMDiff.contMDiffOn`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
H : Type u_…
· 使用引理 `ContMDiff.sumElim`：ContMDiff.sumElim {f : M -> N} {g : M' -> N} (hf : Co
ntMDiff I J n f) (hg : ContMDiff I J n g) : ContMDiff I J n (Sum.elim f g)
· 使用定理 `contMDiff_id`：contMDiff_id : ContMDiff I I n (id : M -> M)
· 使用定理 `contMDiff_const`：contMDiff_const : ContMDiff I I' n fun _ : M => c
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `trivial`：True
-/
lemma contMDiff_of_contMDiff_inl {f : M → N}
    (h : ContMDiff I J n ((@Sum.inl N N') ∘ f)) : ContMDiff I J n f := by
  nontriviality N
  inhabit N
  let aux : N ⊕ N' → N := Sum.elim (@id N) (fun _ ↦ inhabited_h.default)
  have : aux ∘ (@Sum.inl N N') ∘ f = f := by ext; simp [aux]
  rw [← this]
  rw [← contMDiffOn_univ] at h ⊢
  apply (contMDiff_id.sumElim contMDiff_const).contMDiffOn (s := @Sum.inl N N' '' univ).comp h
  intro x _hx
  rw [mem_preimage, Function.comp_apply]
  use f x, trivial
/-
**contMDiff_of_contMDiff_inr** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：contMDiff_of_contMDiff_inr {g : M' -> N'} (h : ContMDiff I J n ((@Sum.inr 
N N') ∘ g)) : ContMDiff I J n g
参数：h : ContMDiff I J n ((@Sum.inr N N') ∘ g)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `contMDiffOn_univ`：contMDiffOn_univ : ContMDiffOn I I' n f univ ↔ ContMDi
ff I I' n f
· 使用定理 `ContMDiffOn.comp`：ContMDiffOn.comp {t : Set M'} {g : M' -> M''} (hg : Co
ntMDiffOn I' I'' n g t) (hf : ContMDiffOn I I' n f s) (st : s subseteq f ⁻¹' t) 
: Cont…
· 使用定理 `ContMDiff.contMDiffOn`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
H : Type u_…
· 使用引理 `ContMDiff.sumElim`：ContMDiff.sumElim {f : M -> N} {g : M' -> N} (hf : Co
ntMDiff I J n f) (hg : ContMDiff I J n g) : ContMDiff I J n (Sum.elim f g)
· 使用定理 `contMDiff_const`：contMDiff_const : ContMDiff I I' n fun _ : M => c
· 使用定理 `contMDiff_id`：contMDiff_id : ContMDiff I I n (id : M -> M)
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `trivial`：True
-/
lemma contMDiff_of_contMDiff_inr {g : M' → N'}
    (h : ContMDiff I J n ((@Sum.inr N N') ∘ g)) : ContMDiff I J n g := by
  nontriviality N'
  inhabit N'
  let aux : N ⊕ N' → N' := Sum.elim (fun _ ↦ inhabited_h.default) (@id N')
  have : aux ∘ (@Sum.inr N N') ∘ g = g := by ext; simp [aux]
  rw [← this]
  rw [← contMDiffOn_univ] at h ⊢
  apply ((contMDiff_const.sumElim contMDiff_id).contMDiffOn (s := Sum.inr '' univ)).comp h
  intro x _hx
  rw [mem_preimage, Function.comp_apply]
  use g x, trivial
/-
**contMDiff_sum_map** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：contMDiff_sum_map {f : M -> N} {g : M' -> N'} : ContMDiff I J n (Sum.map f
 g) ↔ ContMDiff I J n f ∧ ContMDiff I J n g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `contMDiff_of_contMDiff_inl`：contMDiff_of_contMDiff_inl {f : M -> N} (h :
 ContMDiff I J n ((@Sum.inl N N') ∘ f)) : ContMDiff I J n f
· 使用定理 `ContMDiff.comp`：ContMDiff.comp {g : M' -> M''} (hg : ContMDiff I' I'' n 
g) (hf : ContMDiff I I' n f) : ContMDiff I I'' n (g ∘ f)
· 使用引理 `ContMDiff.inl`：ContMDiff.inl : ContMDiff I I n (@Sum.inl M M')
· 使用引理 `contMDiff_of_contMDiff_inr`：contMDiff_of_contMDiff_inr {g : M' -> N'} (h
 : ContMDiff I J n ((@Sum.inr N N') ∘ g)) : ContMDiff I J n g
· 使用引理 `ContMDiff.inr`：ContMDiff.inr : ContMDiff I I n (@Sum.inr M M')
· 使用引理 `ContMDiff.sumMap`：ContMDiff.sumMap {f : M -> N} {g : M' -> N'} (hf : Con
tMDiff I J n f) (hg : ContMDiff I J n g) : ContMDiff I J n (Sum.map f g)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma contMDiff_sum_map {f : M → N} {g : M' → N'} :
    ContMDiff I J n (Sum.map f g) ↔ ContMDiff I J n f ∧ ContMDiff I J n g :=
  ⟨fun h ↦ ⟨contMDiff_of_contMDiff_inl (h.comp ContMDiff.inl),
    contMDiff_of_contMDiff_inr (h.comp ContMDiff.inr)⟩,
   fun h ↦ ContMDiff.sumMap h.1 h.2⟩
/-
**ContMDiff.swap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContMDiff.swap : ContMDiff I I n (@Sum.swap M M')
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContMDiff.sumElim`：ContMDiff.sumElim {f : M -> N} {g : M' -> N} (hf : Co
ntMDiff I J n f) (hg : ContMDiff I J n g) : ContMDiff I J n (Sum.elim f g)
· 使用引理 `ContMDiff.inr`：ContMDiff.inr : ContMDiff I I n (@Sum.inr M M')
· 使用引理 `ContMDiff.inl`：ContMDiff.inl : ContMDiff I I n (@Sum.inl M M')
-/
lemma ContMDiff.swap : ContMDiff I I n (@Sum.swap M M') := ContMDiff.sumElim inr inl

end disjointUnion

