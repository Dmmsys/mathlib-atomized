/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Patrick Massot, Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.Notation

/-!
# Differentiability of functions in vector bundles

-/

public section

open Bundle Set ContinuousLinearMap Pretrivialization Filter
open scoped Manifold Topology

section


variable {𝕜 B B' F M : Type*} {E : B → Type*}

variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)] {EB : Type*}
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  (IB : ModelWithCorners 𝕜 EB HB) (E' : B → Type*) [∀ x, Zero (E' x)] {EM : Type*}
  [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  {n : ℕ∞}

variable [TopologicalSpace B] [ChartedSpace HB B] [FiberBundle F E]


/-- Characterization of differentiable functions into a vector bundle.
Version at a point within a set -/
/-
**mdifferentiableWithinAt_totalSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableWithinAt_totalSpace (f : M -> TotalSpace F E) {s : Set M} {
x₀ : M} : MDiffAt[s] f x₀ ↔ MDiffAt[s] (fun x => (f x).proj) x₀ ∧ MDiffAt[s] (fu
n x => (trivializationAt F E (f x₀).proj (f x)).2) x₀
参数：f : M -> TotalSpace F E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_and_and_comm`：∀ {a b c d : Prop}, (a ∧ b) ∧ c ∧ d ↔ (a ∧ c) ∧ b ∧ d
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FiberBundle.continuousWithinAt_totalSpace`：continuousWithinAt_totalSpace
 (f : X -> TotalSpace F E) {s : Set X} {x₀ : X} : ContinuousWithinAt f s x₀ ↔ Co
ntinuousWithinAt (fun x => (f x…
· 使用定理 `and_congr_right_iff`：∀ {a b c : Prop}, (a ∧ b ↔ a ∧ c) ↔ a → (b ↔ c)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `modelWithCornersSelf_prod`：modelWithCornersSelf_prod : 𝓘(𝕜, E × F) = 𝓘(𝕜
, E).prod 𝓘(𝕜, F)
· 使用定理 `FiberBundle.extChartAt`：∀ {𝕜 : Type u_1} {B : Type u_2} {F : Type u_4} {
E : B → Type u_6} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGr
oup F] [inst…
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `mdifferentiableWithinAt_prod_iff`：mdifferentiableWithinAt_prod_iff (f : 
M -> M' × N') : MDiffAt[s] f x ↔ MDiffAt[s] (Prod.fst ∘ f) x ∧ MDiffAt[s] (Prod.
snd ∘ f) x
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `ContinuousWithinAt.comp`：ContinuousWithinAt.comp {g : β -> γ} {t : Set β
} (hg : ContinuousWithinAt g t (f x)) (hf : ContinuousWithinAt f s x) (h : MapsT
o f s t) : Co…
· 使用定理 `Continuous.continuousWithinAt`：Continuous.continuousWithinAt (h : Contin
uous f) : ContinuousWithinAt f s x
· 使用定理 `FiberBundle.continuous_proj`：continuous_proj : Continuous (π F E)
· 使用定理 `Set.mapsTo_image`：mapsTo_image (f : α -> β) (s : Set α) : MapsTo f s (f 
'' s)
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Bundle.Trivialization.open_baseSet`：∀ {B : Type u_1} {F : Type u_2} {Z :
 Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 :
 TopologicalSpace Z] {pr…
· 使用定理 `FiberBundle.mem_baseSet_trivializationAt`：mem_baseSet_trivializationAt :
 b in (trivializationAt F E b).baseSet
· 使用定理 `Filter.EventuallyEq.mdifferentiableWithinAt_iff`：Filter.EventuallyEq.mdi
fferentiableWithinAt_iff (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : MDiffAt[s] f
 x ↔ MDiffAt[s] f₁ x
· 使用定理 `Filter.eventually_of_mem`：eventually_of_mem {f : Filter α} {P : α -> Pro
p} {U : Set α} (hU : U in f) (h : forall x in U, P x) : forallᶠ x in f, P x
· 使用定理 `Bundle.Trivialization.coe_fst'`：∀ {B : Type u_1} {F : Type u_2} {Z : Typ
e u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z → B} 
  [inst_2 : Topologi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Bundle.Trivialization.coe_fst`：∀ {B : Type u_1} {F : Type u_2} {Z : Type
 u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z → B}  
 [inst_2 : Topologi…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Characterization of differentiable functions into a vector bundle.
Version at a point within a set
-/
theorem mdifferentiableWithinAt_totalSpace (f : M → TotalSpace F E) {s : Set M} {x₀ : M} :
    MDiffAt[s] f x₀ ↔
      MDiffAt[s] (fun x => (f x).proj) x₀ ∧
      MDiffAt[s] (fun x ↦ (trivializationAt F E (f x₀).proj (f x)).2) x₀ := by
  simp +singlePass only [mdifferentiableWithinAt_iff_target]
  rw [and_and_and_comm, ← FiberBundle.continuousWithinAt_totalSpace, and_congr_right_iff]
  intro hf
  simp_rw +instances [modelWithCornersSelf_prod, FiberBundle.extChartAt, Function.comp_def,
    PartialEquiv.trans_apply, PartialEquiv.prod_coe, PartialEquiv.refl_coe,
    extChartAt_self_apply, modelWithCornersSelf_coe, Function.id_def, ← chartedSpaceSelf_prod]
  refine (mdifferentiableWithinAt_prod_iff _).trans (and_congr ?_ Iff.rfl)
  have h1 : (fun x => (f x).proj) ⁻¹' (trivializationAt F E (f x₀).proj).baseSet ∈ 𝓝[s] x₀ :=
    ((FiberBundle.continuous_proj F E).continuousWithinAt.comp hf (mapsTo_image f s))
      ((Trivialization.open_baseSet _).mem_nhds (mem_baseSet_trivializationAt F E _))
  refine EventuallyEq.mdifferentiableWithinAt_iff (eventually_of_mem h1 fun x hx => ?_) ?_
  · simp_rw [Function.comp, OpenPartialHomeomorph.coe_toPartialEquiv, Trivialization.coe_coe]
    rw [Trivialization.coe_fst']
    exact hx
  · simp only [mfld_simps]

/-- Characterization of differentiable functions into a vector bundle.
Version at a point -/
/-
**mdifferentiableAt_totalSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableAt_totalSpace (f : M -> TotalSpace F E) {x₀ : M} : MDiffAt 
f x₀ ↔ MDiffAt (fun x => (f x).proj) x₀ ∧ MDiffAt (fun x => (trivializationAt F 
E (f x₀).proj (f x)).2) x₀
参数：f : M -> TotalSpace F E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mdifferentiableWithinAt_totalSpace`：mdifferentiableWithinAt_totalSpace (
f : M -> TotalSpace F E) {s : Set M} {x₀ : M} : MDiffAt[s] f x₀ ↔ MDiffAt[s] (fu
n x => (f x).proj) x₀ ∧ …

--- 原说明 ---
Characterization of differentiable functions into a vector bundle.
Version at a point
-/
theorem mdifferentiableAt_totalSpace (f : M → TotalSpace F E) {x₀ : M} :
    MDiffAt f x₀ ↔
      MDiffAt (fun x => (f x).proj) x₀ ∧
      MDiffAt (fun x ↦ (trivializationAt F E (f x₀).proj (f x)).2) x₀ := by
  simpa [← mdifferentiableWithinAt_univ] using mdifferentiableWithinAt_totalSpace _ f

/-- Characterization of differentiable sections of a vector bundle at a point within a set
in terms of the preferred trivialization at that point. -/
/-
**mdifferentiableWithinAt_section** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableWithinAt_section (s : Π b, E b) {u : Set B} {b₀ : B} : MDif
fAt[u] (T% s) b₀ ↔ MDiffAt[u] (fun b => (trivializationAt F E b₀ (s b)).2) b₀
参数：s : Π b, E b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mdifferentiableWithinAt_totalSpace`：mdifferentiableWithinAt_totalSpace (
f : M -> TotalSpace F E) {s : Set M} {x₀ : M} : MDiffAt[s] f x₀ ↔ MDiffAt[s] (fu
n x => (f x).proj) x₀ ∧ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Characterization of differentiable sections of a vector bundle at a point within
 a set
in terms of the preferred trivialization at that point.
-/
theorem mdifferentiableWithinAt_section (s : Π b, E b) {u : Set B} {b₀ : B} :
    MDiffAt[u] (T% s) b₀ ↔ MDiffAt[u] (fun b ↦ (trivializationAt F E b₀ (s b)).2) b₀ := by
  rw [mdifferentiableWithinAt_totalSpace]
  change MDifferentiableWithinAt _ _ id _ _ ∧ _ ↔ _
  simp [mdifferentiableWithinAt_id]

/-- Characterization of differentiable sections of a vector bundle at a point within a set
in terms of the preferred trivialization at that point. -/
/-
**mdifferentiableAt_section** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableAt_section (s : Π b, E b) {b₀ : B} : MDiffAt (T% s) b₀ ↔ MD
iffAt (fun b => (trivializationAt F E b₀ (s b)).2) b₀
参数：s : Π b, E b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mdifferentiableWithinAt_section`：mdifferentiableWithinAt_section (s : Π 
b, E b) {u : Set B} {b₀ : B} : MDiffAt[u] (T% s) b₀ ↔ MDiffAt[u] (fun b => (triv
ializationAt F E b₀ (…

--- 原说明 ---
Characterization of differentiable sections of a vector bundle at a point within
 a set
in terms of the preferred trivialization at that point.
-/
theorem mdifferentiableAt_section (s : Π b, E b) {b₀ : B} :
    MDiffAt (T% s) b₀ ↔ MDiffAt (fun b ↦ (trivializationAt F E b₀ (s b)).2) b₀ := by
  simpa [← mdifferentiableWithinAt_univ] using mdifferentiableWithinAt_section _ _

namespace Bundle

variable (E) {IB}

/-
**Bundle.mdifferentiable_proj** 是 Mathlib 中的一个定理，位于命名空间 `Bundle`。
形式化陈述：mdifferentiable_proj : MDiff (π F E)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mdifferentiableAt_id`：mdifferentiableAt_id : MDiffAt (@id M) x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mdifferentiableAt_totalSpace`：mdifferentiableAt_totalSpace (f : M -> Tot
alSpace F E) {x₀ : M} : MDiffAt f x₀ ↔ MDiffAt (fun x => (f x).proj) x₀ ∧ MDiffA
t (fun x => (trivi…
-/
theorem mdifferentiable_proj : MDiff (π F E) := fun x ↦ by
  have : MDiffAt (@id <| TotalSpace F E) x := mdifferentiableAt_id
  rw [mdifferentiableAt_totalSpace] at this
  exact this.1
/-
**Bundle.mdifferentiableOn_proj** 是 Mathlib 中的一个定理，位于命名空间 `Bundle`。
形式化陈述：mdifferentiableOn_proj {s : Set (TotalSpace F E)} : MDiff[s] (π F E)
参数：TotalSpace F E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiable.mdifferentiableOn`：MDifferentiable.mdifferentiableOn (h 
: MDiff f) : MDiff[s] f
· 使用定理 `Bundle.mdifferentiable_proj`：mdifferentiable_proj : MDiff (π F E)
-/
theorem mdifferentiableOn_proj {s : Set (TotalSpace F E)} : MDiff[s] (π F E) :=
  (mdifferentiable_proj E).mdifferentiableOn
/-
**Bundle.mdifferentiableAt_proj** 是 Mathlib 中的一个定理，位于命名空间 `Bundle`。
形式化陈述：mdifferentiableAt_proj {p : TotalSpace F E} : MDiffAt (π F E) p
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiable.mdifferentiableAt`：MDifferentiable.mdifferentiableAt (hf
 : MDiff f) : MDiffAt f x
· 使用定理 `Bundle.mdifferentiable_proj`：mdifferentiable_proj : MDiff (π F E)
-/
theorem mdifferentiableAt_proj {p : TotalSpace F E} : MDiffAt (π F E) p :=
  (mdifferentiable_proj E).mdifferentiableAt
/-
**Bundle.mdifferentiableWithinAt_proj** 是 Mathlib 中的一个定理，位于命名空间 `Bundle`。
形式化陈述：mdifferentiableWithinAt_proj {s : Set (TotalSpace F E)} {p : TotalSpace F 
E} : MDiffAt[s] (π F E) p
参数：TotalSpace F E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableAt.mdifferentiableWithinAt`：MDifferentiableAt.mdifferenti
ableWithinAt (h : MDiffAt f x) : MDiffAt[s] f x
· 使用定理 `Bundle.mdifferentiableAt_proj`：mdifferentiableAt_proj {p : TotalSpace F 
E} : MDiffAt (π F E) p
-/
theorem mdifferentiableWithinAt_proj {s : Set (TotalSpace F E)} {p : TotalSpace F E} :
    MDiffAt[s] (π F E) p :=
  (mdifferentiableAt_proj E).mdifferentiableWithinAt

section

variable (𝕜) [∀ x, AddCommMonoid (E x)]
variable [∀ x, Module 𝕜 (E x)] [VectorBundle 𝕜 F E]

/-
**Bundle.mdifferentiable_zeroSection** 是 Mathlib 中的一个定理，位于命名空间 `Bundle`。
形式化陈述：mdifferentiable_zeroSection : MDiff (zeroSection F E)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mdifferentiableAt_section`：mdifferentiableAt_section (s : Π b, E b) {b₀ 
: B} : MDiffAt (T% s) b₀ ↔ MDiffAt (fun b => (trivializationAt F E b₀ (s b)).2) 
b₀
· 使用定理 `MDifferentiableAt.congr_of_eventuallyEq`：MDifferentiableAt.congr_of_even
tuallyEq (h : MDiffAt f x) (hL : f₁ =ᶠ[𝓝 x] f) : MDiffAt f₁ x
· 使用定理 `mdifferentiableAt_const`：mdifferentiableAt_const : MDiffAt (fun _ : M =>
 c) x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Bundle.Trivialization.open_baseSet`：∀ {B : Type u_1} {F : Type u_2} {Z :
 Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 :
 TopologicalSpace Z] {pr…
· 使用定理 `FiberBundle.mem_baseSet_trivializationAt`：mem_baseSet_trivializationAt :
 b in (trivializationAt F E b).baseSet
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Bundle.Trivialization.zeroSection`：∀ (R : Type u_1) {B : Type u_2} {F : 
Type u_3} {E : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x :
 B) → AddCommMonoid (E …
· 使用定理 `trivialization_linear`：∀ (R : Type u_1) {B : Type u_2} {F : Type u_3} {E
 : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x : B) → AddCom
mMonoid (E …
· 使用定理 `instMemTrivializationAtlasTrivializationAt`：∀ {B : Type u_2} {F : Type u
_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {E : B → Type u_5}
   [inst_2 : TopologicalSpace (B…
-/
theorem mdifferentiable_zeroSection : MDiff (zeroSection F E) := by
  intro x
  unfold zeroSection
  rw [mdifferentiableAt_section]
  apply (mdifferentiableAt_const (c := 0)).congr_of_eventuallyEq
  filter_upwards [(trivializationAt F E x).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt F E x)] with y hy
    using congr_arg Prod.snd <| (trivializationAt F E x).zeroSection 𝕜 hy
/-
**Bundle.mdifferentiableOn_zeroSection** 是 Mathlib 中的一个定理，位于命名空间 `Bundle`。
形式化陈述：mdifferentiableOn_zeroSection {t : Set B} : MDiff[t] (zeroSection F E)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiable.mdifferentiableOn`：MDifferentiable.mdifferentiableOn (h 
: MDiff f) : MDiff[s] f
· 使用定理 `Bundle.mdifferentiable_zeroSection`：mdifferentiable_zeroSection : MDiff 
(zeroSection F E)
-/
theorem mdifferentiableOn_zeroSection {t : Set B} : MDiff[t] (zeroSection F E) :=
  (mdifferentiable_zeroSection _ _).mdifferentiableOn
/-
**Bundle.mdifferentiableAt_zeroSection** 是 Mathlib 中的一个定理，位于命名空间 `Bundle`。
形式化陈述：mdifferentiableAt_zeroSection {x : B} : MDiffAt (zeroSection F E) x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiable.mdifferentiableAt`：MDifferentiable.mdifferentiableAt (hf
 : MDiff f) : MDiffAt f x
· 使用定理 `Bundle.mdifferentiable_zeroSection`：mdifferentiable_zeroSection : MDiff 
(zeroSection F E)
-/
theorem mdifferentiableAt_zeroSection {x : B} : MDiffAt (zeroSection F E) x :=
  (mdifferentiable_zeroSection _ _).mdifferentiableAt
/-
**Bundle.mdifferentiableWithinAt_zeroSection** 是 Mathlib 中的一个定理，位于命名空间 `Bundle`。
形式化陈述：mdifferentiableWithinAt_zeroSection {t : Set B} {x : B} : MDiffAt[t] (zero
Section F E) x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableAt.mdifferentiableWithinAt`：MDifferentiableAt.mdifferenti
ableWithinAt (h : MDiffAt f x) : MDiffAt[s] f x
· 使用定理 `Bundle.mdifferentiable_zeroSection`：mdifferentiable_zeroSection : MDiff 
(zeroSection F E)
-/
theorem mdifferentiableWithinAt_zeroSection {t : Set B} {x : B} :
    MDiffAt[t] (zeroSection F E) x :=
  (mdifferentiable_zeroSection _ _ x).mdifferentiableWithinAt

end

variable {s : ∀ x, E x} {u : Set B} {x : B}

@[nontriviality]
/-
**Bundle.mdifferentiableWithinAt_section_of_subsingleton** 是 Mathlib 中的一个引理，位于命名
空间 `Bundle`。
形式化陈述：mdifferentiableWithinAt_section_of_subsingleton [Subsingleton F] : MDiffAt
[u] (T% s) x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffWithinAt.mdifferentiableWithinAt`：ContMDiffWithinAt.mdifferenti
ableWithinAt (hf : CMDiffAt[s] n f x) (hn : n != 0) : MDiffAt[s] f x
· 使用引理 `Bundle.contMDiffWithinAt_section_of_subsingleton`：contMDiffWithinAt_sect
ion_of_subsingleton [Subsingleton F] : ContMDiffWithinAt IB (IB.prod 𝓘(𝕜, F)) n 
(fun x => TotalSpace.mk' F x (s x)) u …
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
-/
lemma mdifferentiableWithinAt_section_of_subsingleton [Subsingleton F] :
    MDiffAt[u] (T% s) x :=
  (contMDiffWithinAt_section_of_subsingleton _).mdifferentiableWithinAt one_ne_zero

@[nontriviality]
/-
**Bundle.mdifferentiableAt_section_of_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 `Bu
ndle`。
形式化陈述：mdifferentiableAt_section_of_subsingleton [Subsingleton F] : MDiffAt (T% s
) x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mdifferentiableWithinAt_univ`：mdifferentiableWithinAt_univ : MDiffAt[uni
v] f x ↔ MDiffAt f x
· 使用引理 `Bundle.mdifferentiableWithinAt_section_of_subsingleton`：mdifferentiableW
ithinAt_section_of_subsingleton [Subsingleton F] : MDiffAt[u] (T% s) x
-/
lemma mdifferentiableAt_section_of_subsingleton [Subsingleton F] : MDiffAt (T% s) x := by
  rw [← mdifferentiableWithinAt_univ]
  apply mdifferentiableWithinAt_section_of_subsingleton

@[nontriviality]
/-
**Bundle.mdifferentiableOn_section_of_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 `Bu
ndle`。
形式化陈述：mdifferentiableOn_section_of_subsingleton [Subsingleton F] : MDiff[u] (T% 
s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Bundle.mdifferentiableWithinAt_section_of_subsingleton`：mdifferentiableW
ithinAt_section_of_subsingleton [Subsingleton F] : MDiffAt[u] (T% s) x
-/
lemma mdifferentiableOn_section_of_subsingleton [Subsingleton F] : MDiff[u] (T% s) :=
  fun _x _hx ↦ mdifferentiableWithinAt_section_of_subsingleton ..

@[nontriviality]
/-
**Bundle.mdifferentiable_section_of_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 `Bund
le`。
形式化陈述：mdifferentiable_section_of_subsingleton [Subsingleton F] : MDiff (T% s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Bundle.mdifferentiableAt_section_of_subsingleton`：mdifferentiableAt_sect
ion_of_subsingleton [Subsingleton F] : MDiffAt (T% s) x
-/
lemma mdifferentiable_section_of_subsingleton [Subsingleton F] : MDiff (T% s) :=
  fun _x ↦ mdifferentiableAt_section_of_subsingleton ..

end Bundle

section coordChange

variable [(x : B) → AddCommMonoid (E x)] [(x : B) → Module 𝕜 (E x)]
variable (e e' : Trivialization F (π F E)) [MemTrivializationAtlas e] [MemTrivializationAtlas e']
  [VectorBundle 𝕜 F E] [ContMDiffVectorBundle 1 F E IB]
variable {IB}

/-
**mdifferentiableOn_coordChangeL** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableOn_coordChangeL : MDiff[e.baseSet inter e'.baseSet] (fun b 
: B => (e.coordChangeL 𝕜 e' b : F ->L[𝕜] F))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffOn.mdifferentiableOn`：ContMDiffOn.mdifferentiableOn (hf : CMDif
f[s] n f) (hn : n != 0) : MDiff[s] f
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `trivialization_linear`：∀ (R : Type u_1) {B : Type u_2} {F : Type u_3} {E
 : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x : B) → AddCom
mMonoid (E …
· 使用定理 `contMDiffOn_coordChangeL`：contMDiffOn_coordChangeL : ContMDiffOn IB 𝓘(𝕜,
 F ->L[𝕜] F) n (fun b : B => (e.coordChangeL 𝕜 e' b : F ->L[𝕜] F)) (e.baseSet in
ter e'.baseSet…
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
-/
theorem mdifferentiableOn_coordChangeL :
    MDiff[e.baseSet ∩ e'.baseSet] (fun b : B ↦ (e.coordChangeL 𝕜 e' b : F →L[𝕜] F)) :=
  (contMDiffOn_coordChangeL e e').mdifferentiableOn one_ne_zero
/-
**mdifferentiableOn_symm_coordChangeL** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableOn_symm_coordChangeL : MDiff[e.baseSet inter e'.baseSet] (f
un b : B => ((e.coordChangeL 𝕜 e' b).symm : F ->L[𝕜] F))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffOn.mdifferentiableOn`：ContMDiffOn.mdifferentiableOn (hf : CMDif
f[s] n f) (hn : n != 0) : MDiff[s] f
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `trivialization_linear`：∀ (R : Type u_1) {B : Type u_2} {F : Type u_3} {E
 : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x : B) → AddCom
mMonoid (E …
· 使用定理 `contMDiffOn_symm_coordChangeL`：contMDiffOn_symm_coordChangeL : ContMDiff
On IB 𝓘(𝕜, F ->L[𝕜] F) n (fun b : B => ((e.coordChangeL 𝕜 e' b).symm : F ->L[𝕜] 
F)) (e.baseSet inte…
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
-/
theorem mdifferentiableOn_symm_coordChangeL :
    MDiff[e.baseSet ∩ e'.baseSet] (fun b : B ↦ ((e.coordChangeL 𝕜 e' b).symm : F →L[𝕜] F)) :=
  (contMDiffOn_symm_coordChangeL e e').mdifferentiableOn one_ne_zero

variable {e e'}
/-
**mdifferentiableAt_coordChangeL** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableAt_coordChangeL {x : B} (h : x in e.baseSet) (h' : x in e'.
baseSet) : MDiffAt (fun b : B => (e.coordChangeL 𝕜 e' b : F ->L[𝕜] F)) x
参数：h : x in e.baseSet；h' : x in e'.baseSet。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffAt.mdifferentiableAt`：ContMDiffAt.mdifferentiableAt (hf : CMDif
fAt n f x) (hn : n != 0) : MDiffAt f x
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `trivialization_linear`：∀ (R : Type u_1) {B : Type u_2} {F : Type u_3} {E
 : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x : B) → AddCom
mMonoid (E …
· 使用定理 `contMDiffAt_coordChangeL`：contMDiffAt_coordChangeL {x : B} (h : x in e.b
aseSet) (h' : x in e'.baseSet) : ContMDiffAt IB 𝓘(𝕜, F ->L[𝕜] F) n (fun b : B =>
 (e.coordChang…
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
-/
theorem mdifferentiableAt_coordChangeL {x : B}
    (h : x ∈ e.baseSet) (h' : x ∈ e'.baseSet) :
    MDiffAt (fun b : B ↦ (e.coordChangeL 𝕜 e' b : F →L[𝕜] F)) x :=
  (contMDiffAt_coordChangeL h h').mdifferentiableAt one_ne_zero

variable {s : Set M} {f : M → B} {g : M → F} {x : M}
/-
**MDifferentiableWithinAt.coordChangeL** 是 Mathlib 中的一个定理，位于命名空间 `MDifferentiabl
eWithinAt`。
形式化陈述：∀ {𝕜 : Type u_1} {B : Type u_2} {F : Type u_4} {M : Type u_5} {E : B → Typ
e u_6} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup F] [ins
t_2 : NormedSpace 𝕜 F] [inst_3 : TopologicalSpace (Bundle.TotalSpace F E)]   [in
st_4 : (x : B) → TopologicalSpace (E x)] {EB : Type u_7} [inst_5 : NormedAddComm
Group EB]   [inst_6 : NormedSpace 𝕜 EB] {HB : Type u_8} [inst_7 : TopologicalSpa
ce HB] {IB : ModelWithCorners 𝕜 EB HB}   {EM : Type u_10} [inst_8 : NormedAddCom
mGroup EM] [inst_9 : NormedSpace 𝕜 EM] {HM : Type u_11}   [inst_10 : Topological
Space HM] {IM : ModelWithCorners 𝕜 EM HM} [inst_11 : TopologicalSpace M]   [inst
_12 : ChartedSpace HM M] [inst_13 : TopologicalSpace B] [inst_14 : ChartedSpace 
HB B] [inst_15 : FiberBundle F E]   [inst_16 : (x : B) → AddCommMonoid (E x)] [i
nst_17 : (x : B) → _root_.Module 𝕜 (E x)]   {e e' : Bundle.Trivialization F Bund
le.TotalSpace.proj} [inst_18 : MemTrivializationAtlas e]   [inst_19 : MemTrivial
izationAtlas e'] [inst_20 : VectorBundle 𝕜 F E] [ContMDiffVectorBundle 1 F E IB]
 {s : Set M}   {f : M → B} {x : M},   MDiffAt[s] f x →     f x ∈ e.baseSet → f x
 ∈ e'.baseSet → (MDiffAt[s] fun y => ↑(Bundle.Trivialization.coordChangeL 𝕜 e e'
 (f y))) x
参数：Bundle.TotalSpace F E；x : B；E x；x : B；E x；x : B；E x；MDiffAt[s] fun y => ↑(Bun
dle.Trivialization.coordChangeL 𝕜 e e' (f y))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableAt.comp_mdifferentiableWithinAt`：MDifferentiableAt.comp_m
differentiableWithinAt (hg : MDiffAt g (f x)) (hf : MDiffAt[s] f x) : MDiffAt[s]
 (g ∘ f) x
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `trivialization_linear`：∀ (R : Type u_1) {B : Type u_2} {F : Type u_3} {E
 : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x : B) → AddCom
mMonoid (E …
· 使用定理 `mdifferentiableAt_coordChangeL`：mdifferentiableAt_coordChangeL {x : B} (
h : x in e.baseSet) (h' : x in e'.baseSet) : MDiffAt (fun b : B => (e.coordChang
eL 𝕜 e' b : F ->L[𝕜]…
-/
protected theorem MDifferentiableWithinAt.coordChangeL (hf : MDiffAt[s] f x)
    (he : f x ∈ e.baseSet) (he' : f x ∈ e'.baseSet) :
    MDiffAt[s] (fun y ↦ (e.coordChangeL 𝕜 e' (f y) : F →L[𝕜] F)) x :=
  (mdifferentiableAt_coordChangeL he he').comp_mdifferentiableWithinAt _ hf
/-
**MDifferentiableAt.coordChangeL** 是 Mathlib 中的一个定理，位于命名空间 `MDifferentiableAt`。
形式化陈述：∀ {𝕜 : Type u_1} {B : Type u_2} {F : Type u_4} {M : Type u_5} {E : B → Typ
e u_6} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup F] [ins
t_2 : NormedSpace 𝕜 F] [inst_3 : TopologicalSpace (Bundle.TotalSpace F E)]   [in
st_4 : (x : B) → TopologicalSpace (E x)] {EB : Type u_7} [inst_5 : NormedAddComm
Group EB]   [inst_6 : NormedSpace 𝕜 EB] {HB : Type u_8} [inst_7 : TopologicalSpa
ce HB] {IB : ModelWithCorners 𝕜 EB HB}   {EM : Type u_10} [inst_8 : NormedAddCom
mGroup EM] [inst_9 : NormedSpace 𝕜 EM] {HM : Type u_11}   [inst_10 : Topological
Space HM] {IM : ModelWithCorners 𝕜 EM HM} [inst_11 : TopologicalSpace M]   [inst
_12 : ChartedSpace HM M] [inst_13 : TopologicalSpace B] [inst_14 : ChartedSpace 
HB B] [inst_15 : FiberBundle F E]   [inst_16 : (x : B) → AddCommMonoid (E x)] [i
nst_17 : (x : B) → _root_.Module 𝕜 (E x)]   {e e' : Bundle.Trivialization F Bund
le.TotalSpace.proj} [inst_18 : MemTrivializationAtlas e]   [inst_19 : MemTrivial
izationAtlas e'] [inst_20 : VectorBundle 𝕜 F E] [ContMDiffVectorBundle 1 F E IB]
 {f : M → B}   {x : M},   MDiffAt f x →     f x ∈ e.baseSet → f x ∈ e'.baseSet →
 (MDiffAt fun y => ↑(Bundle.Trivialization.coordChangeL 𝕜 e e' (f y))) x
参数：Bundle.TotalSpace F E；x : B；E x；x : B；E x；x : B；E x；MDiffAt fun y => ↑(Bundle
.Trivialization.coordChangeL 𝕜 e e' (f y))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableWithinAt.coordChangeL`：∀ {𝕜 : Type u_1} {B : Type u_2} {F
 : Type u_4} {M : Type u_5} {E : B → Type u_6} [inst : NontriviallyNormedField 𝕜
]   [inst_1 : NormedAddCom…
-/
protected theorem MDifferentiableAt.coordChangeL
    (hf : MDiffAt f x) (he : f x ∈ e.baseSet) (he' : f x ∈ e'.baseSet) :
    MDiffAt (fun y ↦ (e.coordChangeL 𝕜 e' (f y) : F →L[𝕜] F)) x :=
  MDifferentiableWithinAt.coordChangeL hf he he'
/-
**MDifferentiableOn.coordChangeL** 是 Mathlib 中的一个定理，位于命名空间 `MDifferentiableOn`。
形式化陈述：∀ {𝕜 : Type u_1} {B : Type u_2} {F : Type u_4} {M : Type u_5} {E : B → Typ
e u_6} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup F] [ins
t_2 : NormedSpace 𝕜 F] [inst_3 : TopologicalSpace (Bundle.TotalSpace F E)]   [in
st_4 : (x : B) → TopologicalSpace (E x)] {EB : Type u_7} [inst_5 : NormedAddComm
Group EB]   [inst_6 : NormedSpace 𝕜 EB] {HB : Type u_8} [inst_7 : TopologicalSpa
ce HB] {IB : ModelWithCorners 𝕜 EB HB}   {EM : Type u_10} [inst_8 : NormedAddCom
mGroup EM] [inst_9 : NormedSpace 𝕜 EM] {HM : Type u_11}   [inst_10 : Topological
Space HM] {IM : ModelWithCorners 𝕜 EM HM} [inst_11 : TopologicalSpace M]   [inst
_12 : ChartedSpace HM M] [inst_13 : TopologicalSpace B] [inst_14 : ChartedSpace 
HB B] [inst_15 : FiberBundle F E]   [inst_16 : (x : B) → AddCommMonoid (E x)] [i
nst_17 : (x : B) → _root_.Module 𝕜 (E x)]   {e e' : Bundle.Trivialization F Bund
le.TotalSpace.proj} [inst_18 : MemTrivializationAtlas e]   [inst_19 : MemTrivial
izationAtlas e'] [inst_20 : VectorBundle 𝕜 F E] [ContMDiffVectorBundle 1 F E IB]
 {s : Set M}   {f : M → B},   MDiff[s] f →     Set.MapsTo f s e.baseSet →       
Set.MapsTo f s e'.baseSet → MDiff[s] fun y => ↑(Bundle.Trivialization.coordChang
eL 𝕜 e e' (f y))
参数：Bundle.TotalSpace F E；x : B；E x；x : B；E x；x : B；E x；Bundle.Trivialization.coo
rdChangeL 𝕜 e e' (f y)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableWithinAt.coordChangeL`：∀ {𝕜 : Type u_1} {B : Type u_2} {F
 : Type u_4} {M : Type u_5} {E : B → Type u_6} [inst : NontriviallyNormedField 𝕜
]   [inst_1 : NormedAddCom…
-/
protected theorem MDifferentiableOn.coordChangeL
    (hf : MDiff[s] f) (he : MapsTo f s e.baseSet) (he' : MapsTo f s e'.baseSet) :
    MDiff[s] (fun y ↦ (e.coordChangeL 𝕜 e' (f y) : F →L[𝕜] F)) :=
  fun x hx ↦ (hf x hx).coordChangeL (he hx) (he' hx)
/-
**MDifferentiable.coordChangeL** 是 Mathlib 中的一个定理，位于命名空间 `MDifferentiable`。
形式化陈述：∀ {𝕜 : Type u_1} {B : Type u_2} {F : Type u_4} {M : Type u_5} {E : B → Typ
e u_6} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup F] [ins
t_2 : NormedSpace 𝕜 F] [inst_3 : TopologicalSpace (Bundle.TotalSpace F E)]   [in
st_4 : (x : B) → TopologicalSpace (E x)] {EB : Type u_7} [inst_5 : NormedAddComm
Group EB]   [inst_6 : NormedSpace 𝕜 EB] {HB : Type u_8} [inst_7 : TopologicalSpa
ce HB] {IB : ModelWithCorners 𝕜 EB HB}   {EM : Type u_10} [inst_8 : NormedAddCom
mGroup EM] [inst_9 : NormedSpace 𝕜 EM] {HM : Type u_11}   [inst_10 : Topological
Space HM] {IM : ModelWithCorners 𝕜 EM HM} [inst_11 : TopologicalSpace M]   [inst
_12 : ChartedSpace HM M] [inst_13 : TopologicalSpace B] [inst_14 : ChartedSpace 
HB B] [inst_15 : FiberBundle F E]   [inst_16 : (x : B) → AddCommMonoid (E x)] [i
nst_17 : (x : B) → _root_.Module 𝕜 (E x)]   {e e' : Bundle.Trivialization F Bund
le.TotalSpace.proj} [inst_18 : MemTrivializationAtlas e]   [inst_19 : MemTrivial
izationAtlas e'] [inst_20 : VectorBundle 𝕜 F E] [ContMDiffVectorBundle 1 F E IB]
 {f : M → B},   MDiff f →     (∀ (x : M), f x ∈ e.baseSet) →       (∀ (x : M), f
 x ∈ e'.baseSet) → MDiff fun y => ↑(Bundle.Trivialization.coordChangeL 𝕜 e e' (f
 y))
参数：Bundle.TotalSpace F E；x : B；E x；x : B；E x；x : B；E x；∀ (x : M), f x ∈ e.baseSe
t；∀ (x : M), f x ∈ e'.baseSet；Bundle.Trivialization.coordChangeL 𝕜 e e' (f y)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableAt.coordChangeL`：∀ {𝕜 : Type u_1} {B : Type u_2} {F : Typ
e u_4} {M : Type u_5} {E : B → Type u_6} [inst : NontriviallyNormedField 𝕜]   [i
nst_1 : NormedAddCom…
-/
protected theorem MDifferentiable.coordChangeL
    (hf : MDiff f) (he : ∀ x, f x ∈ e.baseSet) (he' : ∀ x, f x ∈ e'.baseSet) :
    MDiff (fun y ↦ (e.coordChangeL 𝕜 e' (f y) : F →L[𝕜] F)) :=
  fun x ↦ (hf x).coordChangeL (he x) (he' x)
/-
**MDifferentiableWithinAt.coordChange** 是 Mathlib 中的一个定理，位于命名空间 `MDifferentiable
WithinAt`。
形式化陈述：∀ {𝕜 : Type u_1} {B : Type u_2} {F : Type u_4} {M : Type u_5} {E : B → Typ
e u_6} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup F] [ins
t_2 : NormedSpace 𝕜 F] [inst_3 : TopologicalSpace (Bundle.TotalSpace F E)]   [in
st_4 : (x : B) → TopologicalSpace (E x)] {EB : Type u_7} [inst_5 : NormedAddComm
Group EB]   [inst_6 : NormedSpace 𝕜 EB] {HB : Type u_8} [inst_7 : TopologicalSpa
ce HB] {IB : ModelWithCorners 𝕜 EB HB}   {EM : Type u_10} [inst_8 : NormedAddCom
mGroup EM] [inst_9 : NormedSpace 𝕜 EM] {HM : Type u_11}   [inst_10 : Topological
Space HM] {IM : ModelWithCorners 𝕜 EM HM} [inst_11 : TopologicalSpace M]   [inst
_12 : ChartedSpace HM M] [inst_13 : TopologicalSpace B] [inst_14 : ChartedSpace 
HB B] [inst_15 : FiberBundle F E]   [inst_16 : (x : B) → AddCommMonoid (E x)] [i
nst_17 : (x : B) → _root_.Module 𝕜 (E x)]   {e e' : Bundle.Trivialization F Bund
le.TotalSpace.proj} [MemTrivializationAtlas e] [MemTrivializationAtlas e']   [in
st_20 : VectorBundle 𝕜 F E] [ContMDiffVectorBundle 1 F E IB] {s : Set M} {f : M 
→ B} {g : M → F} {x : M},   MDiffAt[s] f x →     MDiffAt[s] g x → f x ∈ e.baseSe
t → f x ∈ e'.baseSet → (MDiffAt[s] fun y => e.coordChange e' (f y) (g y)) x
参数：Bundle.TotalSpace F E；x : B；E x；x : B；E x；x : B；E x；MDiffAt[s] fun y => e.coo
rdChange e' (f y) (g y)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableWithinAt.congr_of_eventuallyEq`：MDifferentiableWithinAt.c
ongr_of_eventuallyEq (h : MDiffAt[s] f x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f 
x) : MDiffAt[s] f₁ x
· 使用定理 `trivialization_linear`：∀ (R : Type u_1) {B : Type u_2} {F : Type u_3} {E
 : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x : B) → AddCom
mMonoid (E …
· 使用定理 `MDifferentiableWithinAt.clm_apply`：MDifferentiableWithinAt.clm_apply {g 
: M -> F₁ ->L[𝕜] F₂} {f : M -> F₁} {s : Set M} {x : M} (hg : MDiffAt[s] g x) (hf
 : MDiffAt[s] f x) : MD…
· 使用定理 `MDifferentiableWithinAt.coordChangeL`：∀ {𝕜 : Type u_1} {B : Type u_2} {F
 : Type u_4} {M : Type u_5} {E : B → Type u_6} [inst : NontriviallyNormedField 𝕜
]   [inst_1 : NormedAddCom…
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
· 使用定理 `Bundle.Trivialization.open_baseSet`：∀ {B : Type u_1} {F : Type u_2} {Z :
 Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 :
 TopologicalSpace Z] {pr…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MDifferentiableWithinAt.continuousWithinAt`：MDifferentiableWithinAt.cont
inuousWithinAt {f : M -> M'} {s : Set M} {x : M} (hf : MDifferentiableWithinAt I
 I' f s x) : ContinuousWithinAt …
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Bundle.Trivialization.coordChangeL_apply'`：∀ {R : Type u_1} {B : Type u_
2} {F : Type u_3} {E : B → Type u_4} [inst : Semiring R] [inst_1 : TopologicalSp
ace F]   [inst_2 : TopologicalS…
-/
protected theorem MDifferentiableWithinAt.coordChange
    (hf : MDiffAt[s] f x) (hg : MDiffAt[s] g x)
    (he : f x ∈ e.baseSet) (he' : f x ∈ e'.baseSet) :
    MDiffAt[s] (fun y ↦ e.coordChange e' (f y) (g y)) x := by
  refine ((hf.coordChangeL he he').clm_apply hg).congr_of_eventuallyEq ?_ ?_
  · have : e.baseSet ∩ e'.baseSet ∈ 𝓝 (f x) :=
     (e.open_baseSet.inter e'.open_baseSet).mem_nhds ⟨he, he'⟩
    filter_upwards [hf.continuousWithinAt this] with y hy
    exact (Trivialization.coordChangeL_apply' e e' hy (g y)).symm
  · exact (Trivialization.coordChangeL_apply' e e' ⟨he, he'⟩ (g x)).symm
/-
**MDifferentiableAt.coordChange** 是 Mathlib 中的一个定理，位于命名空间 `MDifferentiableAt`。
形式化陈述：∀ {𝕜 : Type u_1} {B : Type u_2} {F : Type u_4} {M : Type u_5} {E : B → Typ
e u_6} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup F] [ins
t_2 : NormedSpace 𝕜 F] [inst_3 : TopologicalSpace (Bundle.TotalSpace F E)]   [in
st_4 : (x : B) → TopologicalSpace (E x)] {EB : Type u_7} [inst_5 : NormedAddComm
Group EB]   [inst_6 : NormedSpace 𝕜 EB] {HB : Type u_8} [inst_7 : TopologicalSpa
ce HB] {IB : ModelWithCorners 𝕜 EB HB}   {EM : Type u_10} [inst_8 : NormedAddCom
mGroup EM] [inst_9 : NormedSpace 𝕜 EM] {HM : Type u_11}   [inst_10 : Topological
Space HM] {IM : ModelWithCorners 𝕜 EM HM} [inst_11 : TopologicalSpace M]   [inst
_12 : ChartedSpace HM M] [inst_13 : TopologicalSpace B] [inst_14 : ChartedSpace 
HB B] [inst_15 : FiberBundle F E]   [inst_16 : (x : B) → AddCommMonoid (E x)] [i
nst_17 : (x : B) → _root_.Module 𝕜 (E x)]   {e e' : Bundle.Trivialization F Bund
le.TotalSpace.proj} [MemTrivializationAtlas e] [MemTrivializationAtlas e']   [in
st_20 : VectorBundle 𝕜 F E] [ContMDiffVectorBundle 1 F E IB] {f : M → B} {g : M 
→ F} {x : M},   MDiffAt f x → MDiffAt g x → f x ∈ e.baseSet → f x ∈ e'.baseSet →
 (MDiffAt fun y => e.coordChange e' (f y) (g y)) x
参数：Bundle.TotalSpace F E；x : B；E x；x : B；E x；x : B；E x；MDiffAt fun y => e.coordC
hange e' (f y) (g y)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableWithinAt.coordChange`：∀ {𝕜 : Type u_1} {B : Type u_2} {F 
: Type u_4} {M : Type u_5} {E : B → Type u_6} [inst : NontriviallyNormedField 𝕜]
   [inst_1 : NormedAddCom…
-/
protected theorem MDifferentiableAt.coordChange
    (hf : MDiffAt f x) (hg : MDiffAt g x)
    (he : f x ∈ e.baseSet) (he' : f x ∈ e'.baseSet) :
    MDiffAt (fun y ↦ e.coordChange e' (f y) (g y)) x :=
  MDifferentiableWithinAt.coordChange hf hg he he'
/-
**MDifferentiableOn.coordChange** 是 Mathlib 中的一个定理，位于命名空间 `MDifferentiableOn`。
形式化陈述：∀ {𝕜 : Type u_1} {B : Type u_2} {F : Type u_4} {M : Type u_5} {E : B → Typ
e u_6} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup F] [ins
t_2 : NormedSpace 𝕜 F] [inst_3 : TopologicalSpace (Bundle.TotalSpace F E)]   [in
st_4 : (x : B) → TopologicalSpace (E x)] {EB : Type u_7} [inst_5 : NormedAddComm
Group EB]   [inst_6 : NormedSpace 𝕜 EB] {HB : Type u_8} [inst_7 : TopologicalSpa
ce HB] {IB : ModelWithCorners 𝕜 EB HB}   {EM : Type u_10} [inst_8 : NormedAddCom
mGroup EM] [inst_9 : NormedSpace 𝕜 EM] {HM : Type u_11}   [inst_10 : Topological
Space HM] {IM : ModelWithCorners 𝕜 EM HM} [inst_11 : TopologicalSpace M]   [inst
_12 : ChartedSpace HM M] [inst_13 : TopologicalSpace B] [inst_14 : ChartedSpace 
HB B] [inst_15 : FiberBundle F E]   [inst_16 : (x : B) → AddCommMonoid (E x)] [i
nst_17 : (x : B) → _root_.Module 𝕜 (E x)]   {e e' : Bundle.Trivialization F Bund
le.TotalSpace.proj} [MemTrivializationAtlas e] [MemTrivializationAtlas e']   [in
st_20 : VectorBundle 𝕜 F E] [ContMDiffVectorBundle 1 F E IB] {s : Set M} {f : M 
→ B} {g : M → F},   MDiff[s] f →     MDiff[s] g → Set.MapsTo f s e.baseSet → Set
.MapsTo f s e'.baseSet → MDiff[s] fun y => e.coordChange e' (f y) (g y)
参数：Bundle.TotalSpace F E；x : B；E x；x : B；E x；x : B；E x；f y；g y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableWithinAt.coordChange`：∀ {𝕜 : Type u_1} {B : Type u_2} {F 
: Type u_4} {M : Type u_5} {E : B → Type u_6} [inst : NontriviallyNormedField 𝕜]
   [inst_1 : NormedAddCom…
-/
protected theorem MDifferentiableOn.coordChange
    (hf : MDiff[s] f) (hg : MDiff[s] g)
    (he : MapsTo f s e.baseSet) (he' : MapsTo f s e'.baseSet) :
    MDiff[s] (fun y ↦ e.coordChange e' (f y) (g y)) := fun x hx ↦
  (hf x hx).coordChange (hg x hx) (he hx) (he' hx)
/-
**MDifferentiable.coordChange** 是 Mathlib 中的一个定理，位于命名空间 `MDifferentiable`。
形式化陈述：∀ {𝕜 : Type u_1} {B : Type u_2} {F : Type u_4} {M : Type u_5} {E : B → Typ
e u_6} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup F] [ins
t_2 : NormedSpace 𝕜 F] [inst_3 : TopologicalSpace (Bundle.TotalSpace F E)]   [in
st_4 : (x : B) → TopologicalSpace (E x)] {EB : Type u_7} [inst_5 : NormedAddComm
Group EB]   [inst_6 : NormedSpace 𝕜 EB] {HB : Type u_8} [inst_7 : TopologicalSpa
ce HB] {IB : ModelWithCorners 𝕜 EB HB}   {EM : Type u_10} [inst_8 : NormedAddCom
mGroup EM] [inst_9 : NormedSpace 𝕜 EM] {HM : Type u_11}   [inst_10 : Topological
Space HM] {IM : ModelWithCorners 𝕜 EM HM} [inst_11 : TopologicalSpace M]   [inst
_12 : ChartedSpace HM M] [inst_13 : TopologicalSpace B] [inst_14 : ChartedSpace 
HB B] [inst_15 : FiberBundle F E]   [inst_16 : (x : B) → AddCommMonoid (E x)] [i
nst_17 : (x : B) → _root_.Module 𝕜 (E x)]   {e e' : Bundle.Trivialization F Bund
le.TotalSpace.proj} [MemTrivializationAtlas e] [MemTrivializationAtlas e']   [in
st_20 : VectorBundle 𝕜 F E] [ContMDiffVectorBundle 1 F E IB] {f : M → B} {g : M 
→ F},   MDiff f →     MDiff g → (∀ (x : M), f x ∈ e.baseSet) → (∀ (x : M), f x ∈
 e'.baseSet) → MDiff fun y => e.coordChange e' (f y) (g y)
参数：Bundle.TotalSpace F E；x : B；E x；x : B；E x；x : B；E x；∀ (x : M), f x ∈ e.baseSe
t；∀ (x : M), f x ∈ e'.baseSet；f y；g y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableAt.coordChange`：∀ {𝕜 : Type u_1} {B : Type u_2} {F : Type
 u_4} {M : Type u_5} {E : B → Type u_6} [inst : NontriviallyNormedField 𝕜]   [in
st_1 : NormedAddCom…
-/
protected theorem MDifferentiable.coordChange
    (hf : MDiff f) (hg : MDiff g) (he : ∀ x, f x ∈ e.baseSet) (he' : ∀ x, f x ∈ e'.baseSet) :
    MDiff (fun y ↦ e.coordChange e' (f y) (g y)) := fun x ↦
  (hf x).coordChange (hg x) (he x) (he' x)

end coordChange

variable [(x : B) → AddCommMonoid (E x)] [(x : B) → Module 𝕜 (E x)]
  [VectorBundle 𝕜 F E] [ContMDiffVectorBundle 1 F E IB]

/-
**MDifferentiableWithinAt.change_section_trivialization** 是 Mathlib 中的一个引理，位于命名空
间 ``。
形式化陈述：MDifferentiableWithinAt.change_section_trivialization {e : Trivialization 
F TotalSpace.proj} [MemTrivializationAtlas e] {e' : Trivialization F TotalSpace.
proj} [MemTrivializationAtlas e'] {f : M -> TotalSpace F E} {s : Set M} {x₀ : M}
 (hf : MDiffAt[s] (π F E ∘ f) x₀) (he'f : MDiffAt[s] (fun x => (e (f x)).2) x₀) 
(he : f x₀ in e.source) (he' : f x₀ in e'.source) : MDiffAt[s] (fun x => (e' (f 
x)).2) x₀
参数：hf : MDiffAt[s] (π F E ∘ f) x₀；he'f : MDiffAt[s] (fun x => (e (f x)).2) x₀；he
 : f x₀ in e.source；he' : f x₀ in e'.source。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableWithinAt.congr_of_eventuallyEq`：MDifferentiableWithinAt.c
ongr_of_eventuallyEq (h : MDiffAt[s] f x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f 
x) : MDiffAt[s] f₁ x
· 使用定理 `MDifferentiableWithinAt.coordChange`：∀ {𝕜 : Type u_1} {B : Type u_2} {F 
: Type u_4} {M : Type u_5} {E : B → Type u_6} [inst : NontriviallyNormedField 𝕜]
   [inst_1 : NormedAddCom…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.Trivialization.mem_source`：∀ {B : Type u_1} {F : Type u_2} {Z : T
ype u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z → B
}   [inst_2 : Topologi…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MDifferentiableWithinAt.continuousWithinAt`：MDifferentiableWithinAt.cont
inuousWithinAt {f : M -> M'} {s : Set M} {x : M} (hf : MDifferentiableWithinAt I
 I' f s x) : ContinuousWithinAt …
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Bundle.Trivialization.open_baseSet`：∀ {B : Type u_1} {F : Type u_2} {Z :
 Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 :
 TopologicalSpace Z] {pr…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Bundle.Trivialization.coordChange_apply_snd`：∀ {B : Type u_1} {F : Type 
u_2} {Z : Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {p
roj : Z → B}   [inst_2 : Topologi…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma MDifferentiableWithinAt.change_section_trivialization
    {e : Trivialization F TotalSpace.proj} [MemTrivializationAtlas e]
    {e' : Trivialization F TotalSpace.proj} [MemTrivializationAtlas e']
    {f : M → TotalSpace F E} {s : Set M} {x₀ : M}
    (hf : MDiffAt[s] (π F E ∘ f) x₀) (he'f : MDiffAt[s] (fun x ↦ (e (f x)).2) x₀)
    (he : f x₀ ∈ e.source) (he' : f x₀ ∈ e'.source) :
    MDiffAt[s] (fun x ↦ (e' (f x)).2) x₀ := by
  rw [Trivialization.mem_source] at he he'
  refine (hf.coordChange he'f he he').congr_of_eventuallyEq ?_ (by simp [he])
  filter_upwards [hf.continuousWithinAt (e.open_baseSet.mem_nhds he)] with y hy
  simp_all

namespace Bundle.Trivialization

/-
**Bundle.Trivialization.mdifferentiableWithinAt_snd_comp_iff** 是 Mathlib 中的一个定理，
位于命名空间 `Bundle.Trivialization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mdifferentiableWithinAt_snd_comp_iff₂
    {e e' : Trivialization F TotalSpace.proj} [MemTrivializationAtlas e] [MemTrivializationAtlas e']
    {f : M → TotalSpace F E} {s : Set M} {x₀ : M}
    (hex₀ : f x₀ ∈ e.source) (he'x₀ : f x₀ ∈ e'.source)
    (hf : MDiffAt[s] (π F E ∘ f) x₀) :
    MDiffAt[s] (fun x ↦ (e (f x)).2) x₀ ↔ MDiffAt[s] (fun x ↦ (e' (f x)).2) x₀ :=
  ⟨(hf.change_section_trivialization IB · hex₀ he'x₀),
   (hf.change_section_trivialization IB · he'x₀ hex₀)⟩

variable (e e')
/-
**Bundle.Trivialization.mdifferentiableAt_snd_comp_iff** 是 Mathlib 中的一个定理，位于命名空间
 `Bundle.Trivialization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mdifferentiableAt_snd_comp_iff₂
    {e e' : Trivialization F TotalSpace.proj} [MemTrivializationAtlas e] [MemTrivializationAtlas e']
    {f : M → TotalSpace F E} {x₀ : M}
    (he : f x₀ ∈ e.source) (he' : f x₀ ∈ e'.source)
    (hf : MDiffAt (fun x ↦ (f x).proj) x₀) :
    MDiffAt (fun x ↦ (e (f x)).2) x₀ ↔ MDiffAt (fun x ↦ (e' (f x)).2) x₀ := by
  simpa [← mdifferentiableWithinAt_univ] using
    e.mdifferentiableWithinAt_snd_comp_iff₂ IB he he' hf

/-- Characterization of differentiable functions into a vector bundle in terms
of any trivialization. Version at a point within a set. -/
/-
**Bundle.Trivialization.mdifferentiableWithinAt_totalSpace_iff** 是 Mathlib 中的一个定
理，位于命名空间 `Bundle.Trivialization`。
形式化陈述：mdifferentiableWithinAt_totalSpace_iff (e : Trivialization F (TotalSpace.p
roj : TotalSpace F E -> B)) [MemTrivializationAtlas e] (f : M -> TotalSpace F E)
 {s : Set M} {x₀ : M} (he : f x₀ in e.source) : MDiffAt[s] f x₀ ↔ MDiffAt[s] (fu
n x => (f x).proj) x₀ ∧ MDiffAt[s] (fun x => (e (f x)).2) x₀
参数：e : Trivialization F (TotalSpace.proj : TotalSpace F E -> B)；f : M -> TotalSp
ace F E；he : f x₀ in e.source。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mdifferentiableWithinAt_totalSpace`：mdifferentiableWithinAt_totalSpace (
f : M -> TotalSpace F E) {s : Set M} {x₀ : M} : MDiffAt[s] f x₀ ↔ MDiffAt[s] (fu
n x => (f x).proj) x₀ ∧ …
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用定理 `Bundle.Trivialization.mdifferentiableWithinAt_snd_comp_iff₂`：mdifferenti
ableWithinAt_snd_comp_iff₂ {e e' : Trivialization F TotalSpace.proj} [MemTrivial
izationAtlas e] [MemTrivializationAtlas e'] {f : …
· 使用定理 `instMemTrivializationAtlasTrivializationAt`：∀ {B : Type u_2} {F : Type u
_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {E : B → Type u_5}
   [inst_2 : TopologicalSpace (B…
· 使用定理 `FiberBundle.mem_trivializationAt_proj_source`：mem_trivializationAt_proj_
source {x : TotalSpace F E} : x in (trivializationAt F E x.proj).source
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Characterization of differentiable functions into a vector bundle in terms
of any trivialization. Version at a point within a set.
-/
theorem mdifferentiableWithinAt_totalSpace_iff
    (e : Trivialization F (TotalSpace.proj : TotalSpace F E → B)) [MemTrivializationAtlas e]
    (f : M → TotalSpace F E) {s : Set M} {x₀ : M}
    (he : f x₀ ∈ e.source) :
    MDiffAt[s] f x₀ ↔
      MDiffAt[s] (fun x ↦ (f x).proj) x₀ ∧ MDiffAt[s] (fun x ↦ (e (f x)).2) x₀ := by
  rw [mdifferentiableWithinAt_totalSpace]
  apply and_congr_right
  intro hf
  rw [Trivialization.mdifferentiableWithinAt_snd_comp_iff₂ IB
    (FiberBundle.mem_trivializationAt_proj_source) he hf]

/-- Characterization of differentiable functions into a vector bundle in terms
of any trivialization. Version at a point. -/
/-
**Bundle.Trivialization.mdifferentiableAt_totalSpace_iff** 是 Mathlib 中的一个定理，位于命名
空间 `Bundle.Trivialization`。
形式化陈述：mdifferentiableAt_totalSpace_iff (e : Trivialization F (TotalSpace.proj : 
TotalSpace F E -> B)) [MemTrivializationAtlas e] (f : M -> TotalSpace F E) {x₀ :
 M} (he : f x₀ in e.source) : MDiffAt f x₀ ↔ MDiffAt (fun x => (f x).proj) x₀ ∧ 
MDiffAt (fun x => (e (f x)).2) x₀
参数：e : Trivialization F (TotalSpace.proj : TotalSpace F E -> B)；f : M -> TotalSp
ace F E；he : f x₀ in e.source。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mdifferentiableAt_totalSpace`：mdifferentiableAt_totalSpace (f : M -> Tot
alSpace F E) {x₀ : M} : MDiffAt f x₀ ↔ MDiffAt (fun x => (f x).proj) x₀ ∧ MDiffA
t (fun x => (trivi…
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用定理 `Bundle.Trivialization.mdifferentiableAt_snd_comp_iff₂`：mdifferentiableAt
_snd_comp_iff₂ {e e' : Trivialization F TotalSpace.proj} [MemTrivializationAtlas
 e] [MemTrivializationAtlas e'] {f : M -> T…
· 使用定理 `instMemTrivializationAtlasTrivializationAt`：∀ {B : Type u_2} {F : Type u
_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {E : B → Type u_5}
   [inst_2 : TopologicalSpace (B…
· 使用定理 `FiberBundle.mem_trivializationAt_proj_source`：mem_trivializationAt_proj_
source {x : TotalSpace F E} : x in (trivializationAt F E x.proj).source
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Characterization of differentiable functions into a vector bundle in terms
of any trivialization. Version at a point.
-/
theorem mdifferentiableAt_totalSpace_iff
    (e : Trivialization F (TotalSpace.proj : TotalSpace F E → B)) [MemTrivializationAtlas e]
    (f : M → TotalSpace F E) {x₀ : M}
    (he : f x₀ ∈ e.source) :
    MDiffAt f x₀ ↔ MDiffAt (fun x ↦ (f x).proj) x₀ ∧ MDiffAt (fun x ↦ (e (f x)).2) x₀ := by
  rw [mdifferentiableAt_totalSpace]
  apply and_congr_right
  intro hf
  rw [Trivialization.mdifferentiableAt_snd_comp_iff₂ IB
    (FiberBundle.mem_trivializationAt_proj_source) he hf]

/-- Characterization of differentiable functions into a vector bundle in terms
of any trivialization. Version at a point within a set. -/
/-
**Bundle.Trivialization.mdifferentiableWithinAt_section_iff** 是 Mathlib 中的一个定理，位
于命名空间 `Bundle.Trivialization`。
形式化陈述：mdifferentiableWithinAt_section_iff (e : Trivialization F (TotalSpace.proj
 : TotalSpace F E -> B)) [MemTrivializationAtlas e] (s : Π b : B, E b) {u : Set 
B} {b₀ : B} (hex₀ : b₀ in e.baseSet) : MDiffAt[u] (T% s) b₀ ↔ MDiffAt[u] (fun x 
=> (e (s x)).2) b₀
参数：e : Trivialization F (TotalSpace.proj : TotalSpace F E -> B)；s : Π b : B, E b
；hex₀ : b₀ in e.baseSet。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.Trivialization.mdifferentiableWithinAt_totalSpace_iff`：mdifferent
iableWithinAt_totalSpace_iff (e : Trivialization F (TotalSpace.proj : TotalSpace
 F E -> B)) [MemTrivializationAtlas e] (f : M -> T…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Bundle.Trivialization.coe_mem_source`：∀ {B : Type u_1} {F : Type u_2} {E
 : B → Type u_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [in
st_2 : TopologicalSpace (B…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Characterization of differentiable functions into a vector bundle in terms
of any trivialization. Version at a point within a set.
-/
theorem mdifferentiableWithinAt_section_iff
    (e : Trivialization F (TotalSpace.proj : TotalSpace F E → B)) [MemTrivializationAtlas e]
    (s : Π b : B, E b) {u : Set B} {b₀ : B}
    (hex₀ : b₀ ∈ e.baseSet) :
    MDiffAt[u] (T% s) b₀ ↔ MDiffAt[u] (fun x ↦ (e (s x)).2) b₀ := by
  rw [e.mdifferentiableWithinAt_totalSpace_iff IB]
  · change MDiffAt[u] (@id B) b₀ ∧ _ ↔ _
    simp [mdifferentiableWithinAt_id]
  exact (coe_mem_source e).mpr hex₀

/-- Characterization of differentiable functions into a vector bundle in terms
of any trivialization. Version at a point. -/
/-
**Bundle.Trivialization.mdifferentiableAt_section_iff** 是 Mathlib 中的一个定理，位于命名空间 
`Bundle.Trivialization`。
形式化陈述：mdifferentiableAt_section_iff (e : Trivialization F (TotalSpace.proj : Tot
alSpace F E -> B)) [MemTrivializationAtlas e] (s : Π b : B, E b) {b₀ : B} (hex₀ 
: b₀ in e.baseSet) : MDiffAt (T% s) b₀ ↔ MDiffAt (fun x => (e (s x)).2) b₀
参数：e : Trivialization F (TotalSpace.proj : TotalSpace F E -> B)；s : Π b : B, E b
；hex₀ : b₀ in e.baseSet。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.Trivialization.mdifferentiableWithinAt_section_iff`：mdifferentiab
leWithinAt_section_iff (e : Trivialization F (TotalSpace.proj : TotalSpace F E -
> B)) [MemTrivializationAtlas e] (s : Π b : B, …

--- 原说明 ---
Characterization of differentiable functions into a vector bundle in terms
of any trivialization. Version at a point.
-/
theorem mdifferentiableAt_section_iff
    (e : Trivialization F (TotalSpace.proj : TotalSpace F E → B)) [MemTrivializationAtlas e]
    (s : Π b : B, E b) {b₀ : B}
    (hex₀ : b₀ ∈ e.baseSet) :
    MDiffAt (T% s) b₀ ↔ MDiffAt (fun x ↦ (e (s x)).2) b₀ := by
  simpa [← mdifferentiableWithinAt_univ] using e.mdifferentiableWithinAt_section_iff IB s hex₀

variable {IB} in
/-- Differentiability of a section on `s` can be determined
using any trivialisation whose `baseSet` contains `s`. -/
/-
**Bundle.Trivialization.mdifferentiableOn_section_iff** 是 Mathlib 中的一个定理，位于命名空间 
`Bundle.Trivialization`。
形式化陈述：mdifferentiableOn_section_iff {s : forall x, E x} {a : Set B} (e : Trivial
ization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F E -> B)) [MemTrivializat
ionAtlas e] (ha : IsOpen a) (ha' : a subseteq e.baseSet) : MDiff[a] (T% s) ↔ MDi
ff[a] (fun x => (e ⟨x, s x⟩).2)
参数：e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F E -> B)；ha
 : IsOpen a；ha' : a subseteq e.baseSet。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableWithinAt.mdifferentiableAt`：MDifferentiableWithinAt.mdiff
erentiableAt (h : MDiffAt[s] f x) (hs : s in 𝓝 x) : MDiffAt f x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `MDifferentiableAt.mdifferentiableWithinAt`：MDifferentiableAt.mdifferenti
ableWithinAt (h : MDiffAt f x) : MDiffAt[s] f x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Bundle.Trivialization.mdifferentiableAt_section_iff`：mdifferentiableAt_s
ection_iff (e : Trivialization F (TotalSpace.proj : TotalSpace F E -> B)) [MemTr
ivializationAtlas e] (s : Π b : B, E b) {…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a

--- 原说明 ---
Differentiability of a section on `s` can be determined
using any trivialisation whose `baseSet` contains `s`.
-/
theorem mdifferentiableOn_section_iff {s : ∀ x, E x} {a : Set B}
    (e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F E → B))
    [MemTrivializationAtlas e] (ha : IsOpen a) (ha' : a ⊆ e.baseSet) :
    MDiff[a] (T% s) ↔ MDiff[a] (fun x ↦ (e ⟨x, s x⟩).2) := by
  refine ⟨fun h x hx ↦ ?_, fun h x hx ↦ ?_⟩ <;>
  have := (h x hx).mdifferentiableAt <| ha.mem_nhds hx
  · exact ((e.mdifferentiableAt_section_iff _ _ (ha' hx)).mp this).mdifferentiableWithinAt
  · exact ((e.mdifferentiableAt_section_iff _ _ (ha' hx)).mpr this).mdifferentiableWithinAt

variable {IB} in
/-- For any trivialization `e`, the differentiability of a section on `e.baseSet`
can be determined using `e`. -/
/-
**Bundle.Trivialization.mdifferentiableOn_section_baseSet_iff** 是 Mathlib 中的一个定理
，位于命名空间 `Bundle.Trivialization`。
形式化陈述：mdifferentiableOn_section_baseSet_iff {s : forall x, E x} (e : Trivializat
ion F (Bundle.TotalSpace.proj : Bundle.TotalSpace F E -> B)) [MemTrivializationA
tlas e] : MDiff[e.baseSet] (T% s) ↔ MDiff[e.baseSet] (fun x => (e ⟨x, s x⟩).2)
参数：e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F E -> B)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Trivialization.mdifferentiableOn_section_iff`：mdifferentiableOn_s
ection_iff {s : forall x, E x} {a : Set B} (e : Trivialization F (Bundle.TotalSp
ace.proj : Bundle.TotalSpace F E -> B)) […
· 使用定理 `Bundle.Trivialization.open_baseSet`：∀ {B : Type u_1} {F : Type u_2} {Z :
 Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 :
 TopologicalSpace Z] {pr…
· 使用定理 `subset_rfl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorde
r α] {a : α}, a ⊆ a

--- 原说明 ---
For any trivialization `e`, the differentiability of a section on `e.baseSet`
can be determined using `e`.
-/
theorem mdifferentiableOn_section_baseSet_iff {s : ∀ x, E x}
    (e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F E → B))
    [MemTrivializationAtlas e] :
    MDiff[e.baseSet] (T% s) ↔ MDiff[e.baseSet] (fun x ↦ (e ⟨x, s x⟩).2) :=
  e.mdifferentiableOn_section_iff e.open_baseSet subset_rfl

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  (Z : M → Type*) [TopologicalSpace (TotalSpace F Z)] [∀ b, TopologicalSpace (Z b)]
  [FiberBundle F Z] [∀ b, AddCommMonoid (Z b)] [∀ b, Module 𝕜 (Z b)] [VectorBundle 𝕜 F Z]

/-
**Bundle.Trivialization.mdifferentiable** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Trivia
lization`。
形式化陈述：mdifferentiable [ContMDiffVectorBundle 1 F Z I] (e : Trivialization F (π F
 Z)) [MemTrivializationAtlas e] : e.MDifferentiable (I.prod 𝓘(𝕜, F)) (I.prod 𝓘(𝕜
, F))
参数：e : Trivialization F (π F Z)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffOn.mdifferentiableOn`：ContMDiffOn.mdifferentiableOn (hf : CMDif
f[s] n f) (hn : n != 0) : MDiff[s] f
· 使用定理 `Bundle.Trivialization.contMDiffOn`：contMDiffOn (e : Trivialization F (π 
F E)) [MemTrivializationAtlas e] : ContMDiffOn (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F
)) n e e.source
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Bundle.Trivialization.contMDiffOn_symm`：contMDiffOn_symm (e : Trivializa
tion F (π F E)) [MemTrivializationAtlas e] : ContMDiffOn (IB.prod 𝓘(𝕜, F)) (IB.p
rod 𝓘(𝕜, F)) n e.toOpenParti…
-/
theorem mdifferentiable [ContMDiffVectorBundle 1 F Z I]
    (e : Trivialization F (π F Z)) [MemTrivializationAtlas e] :
    e.MDifferentiable (I.prod 𝓘(𝕜, F)) (I.prod 𝓘(𝕜, F)) :=
  ⟨e.contMDiffOn.mdifferentiableOn one_ne_zero, e.contMDiffOn_symm.mdifferentiableOn one_ne_zero⟩

set_option linter.dupNamespace false in
@[deprecated (since := "2026-05-24")] alias Bundle.Trivialization.mdifferentiable := mdifferentiable

end

end Bundle.Trivialization

end

section operations

variable {𝕜 B B' F M : Type*} {E : B → Type*}

variable
  -- Let `E` be a fiber bundle with base `B` and fiber `F` (a vector space over `𝕜`)
  [TopologicalSpace B] [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)]
  [NormedAddCommGroup F] [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 F] [FiberBundle F E]
  -- Moreover let `E` be a vector bundle
  [(x : B) → AddCommGroup (E x)] [(x : B) → Module 𝕜 (E x)] [VectorBundle 𝕜 F E]
  -- Let the base `B` be charted over a fixed model space `HB`
  {HB : Type*} [TopologicalSpace HB] [ChartedSpace HB B]
  -- Moreover let `HB` be modelled on a normed space `EB` so that `B` (and hence `E`) have
  -- differentiable structures
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {I : ModelWithCorners 𝕜 EB HB}

variable {f : B → 𝕜} {a : 𝕜} {s t : Π x : B, E x} {u : Set B} {x₀ : B}

/-
**mdifferentiableWithinAt_add_section** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mdifferentiableWithinAt_add_section (hs : MDiffAt[u] (T% s) x₀) (ht : MDif
fAt[u] (T% t) x₀) : MDiffAt[u] (T% (s + t)) x₀
参数：hs : MDiffAt[u] (T% s) x₀；ht : MDiffAt[u] (T% t) x₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mdifferentiableWithinAt_section`：mdifferentiableWithinAt_section (s : Π 
b, E b) {u : Set B} {b₀ : B} : MDiffAt[u] (T% s) b₀ ↔ MDiffAt[u] (fun b => (triv
ializationAt F E b₀ (…
· 使用定理 `MDifferentiableWithinAt.congr_of_eventuallyEq`：MDifferentiableWithinAt.c
ongr_of_eventuallyEq (h : MDiffAt[s] f x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f 
x) : MDiffAt[s] f₁ x
· 使用定理 `MDifferentiableWithinAt.add`：MDifferentiableWithinAt.add {s : Set M} (hf
 : MDiffAt[s] f z) (hg : MDiffAt[s] g z) : MDiffAt[s] (f + g) z
· 使用定理 `Filter.eventually_of_mem`：eventually_of_mem {f : Filter α} {P : α -> Pro
p} {U : Set α} (hU : U in f) (h : forall x in U, P x) : forallᶠ x in f, P x
· 使用定理 `mem_nhdsWithin_of_mem_nhds`：mem_nhdsWithin_of_mem_nhds {s t : Set α} {a 
: α} (h : s in 𝓝 a) : s in 𝓝[t] a
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Bundle.Trivialization.open_baseSet`：∀ {B : Type u_1} {F : Type u_2} {Z :
 Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 :
 TopologicalSpace Z] {pr…
· 使用定理 `FiberBundle.mem_baseSet_trivializationAt`：mem_baseSet_trivializationAt :
 b in (trivializationAt F E b).baseSet
· 使用定理 `IsLinearMap.map_add`：∀ {R : Type u} {M : Type v} {M₂ : Type w} [inst : S
emiring R] [inst_1 : AddCommMonoid M] [inst_2 : AddCommMonoid M₂]   [inst_3 : _r
oot_.Modu…
· 使用定理 `Bundle.Trivialization.linear`：∀ (R : Type u_1) {B : Type u_2} {F : Type 
u_3} {E : B → Type u_4} [inst : Semiring R] [inst_1 : TopologicalSpace F]   [ins
t_2 : TopologicalS…
· 使用定理 `trivialization_linear`：∀ (R : Type u_1) {B : Type u_2} {F : Type u_3} {E
 : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x : B) → AddCom
mMonoid (E …
· 使用定理 `instMemTrivializationAtlasTrivializationAt`：∀ {B : Type u_2} {F : Type u
_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {E : B → Type u_5}
   [inst_2 : TopologicalSpace (B…
· 使用定理 `FiberBundle.mem_baseSet_trivializationAt'`：∀ {B : Type u_2} {F : Type u_
3} {inst : TopologicalSpace B} {inst_1 : TopologicalSpace F} {E : B → Type u_5} 
  {inst_2 : TopologicalSpace (B…
-/
lemma mdifferentiableWithinAt_add_section
    (hs : MDiffAt[u] (T% s) x₀) (ht : MDiffAt[u] (T% t) x₀) :
    MDiffAt[u] (T% (s + t)) x₀ := by
  rw [mdifferentiableWithinAt_section] at hs ht ⊢
  set e := trivializationAt F E x₀
  refine (hs.add ht).congr_of_eventuallyEq ?_ ?_
  · apply eventually_of_mem (U := e.baseSet)
    · exact mem_nhdsWithin_of_mem_nhds <|
        (e.open_baseSet.mem_nhds <| mem_baseSet_trivializationAt F E x₀)
    · exact fun x hx ↦ (e.linear 𝕜 hx).1 ..
  · exact (e.linear 𝕜 (FiberBundle.mem_baseSet_trivializationAt' x₀)).1 ..
/-
**mdifferentiableAt_add_section** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mdifferentiableAt_add_section (hs : MDiffAt (T% s) x₀) (ht : MDiffAt (T% t
) x₀) : MDiffAt (T% (s + t)) x₀
参数：hs : MDiffAt (T% s) x₀；ht : MDiffAt (T% t) x₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mdifferentiableWithinAt_univ`：mdifferentiableWithinAt_univ : MDiffAt[uni
v] f x ↔ MDiffAt f x
· 使用引理 `mdifferentiableWithinAt_add_section`：mdifferentiableWithinAt_add_section
 (hs : MDiffAt[u] (T% s) x₀) (ht : MDiffAt[u] (T% t) x₀) : MDiffAt[u] (T% (s + t
)) x₀
-/
lemma mdifferentiableAt_add_section
    (hs : MDiffAt (T% s) x₀) (ht : MDiffAt (T% t) x₀) :
    MDiffAt (T% (s + t)) x₀ := by
  rw [← mdifferentiableWithinAt_univ] at hs ht ⊢
  apply mdifferentiableWithinAt_add_section hs ht
/-
**mdifferentiableOn_add_section** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mdifferentiableOn_add_section (hs : MDiff[u] (T% s)) (ht : MDiff[u] (T% t)
) : MDiff[u] (T% (s + t))
参数：hs : MDiff[u] (T% s)；ht : MDiff[u] (T% t)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `mdifferentiableWithinAt_add_section`：mdifferentiableWithinAt_add_section
 (hs : MDiffAt[u] (T% s) x₀) (ht : MDiffAt[u] (T% t) x₀) : MDiffAt[u] (T% (s + t
)) x₀
-/
lemma mdifferentiableOn_add_section
    (hs : MDiff[u] (T% s)) (ht : MDiff[u] (T% t)) : MDiff[u] (T% (s + t)) :=
  fun x₀ hx₀ ↦ mdifferentiableWithinAt_add_section (hs x₀ hx₀) (ht x₀ hx₀)
/-
**mdifferentiable_add_section** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mdifferentiable_add_section (hs : MDiff (T% s)) (ht : MDiff (T% t)) : MDif
f (T% (s + t))
参数：hs : MDiff (T% s)；ht : MDiff (T% t)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `mdifferentiableAt_add_section`：mdifferentiableAt_add_section (hs : MDiff
At (T% s) x₀) (ht : MDiffAt (T% t) x₀) : MDiffAt (T% (s + t)) x₀
-/
lemma mdifferentiable_add_section
    (hs : MDiff (T% s)) (ht : MDiff (T% t)) : MDiff (T% (s + t)) :=
  fun x₀ ↦ mdifferentiableAt_add_section (hs x₀) (ht x₀)
/-
**mdifferentiableWithinAt_neg_section** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mdifferentiableWithinAt_neg_section (hs : MDiffAt[u] (T% s) x₀) : MDiffAt[
u] (T% (-s)) x₀
参数：hs : MDiffAt[u] (T% s) x₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mdifferentiableWithinAt_section`：mdifferentiableWithinAt_section (s : Π 
b, E b) {u : Set B} {b₀ : B} : MDiffAt[u] (T% s) b₀ ↔ MDiffAt[u] (fun b => (triv
ializationAt F E b₀ (…
· 使用定理 `MDifferentiableWithinAt.congr_of_eventuallyEq`：MDifferentiableWithinAt.c
ongr_of_eventuallyEq (h : MDiffAt[s] f x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f 
x) : MDiffAt[s] f₁ x
· 使用定理 `MDifferentiableWithinAt.neg`：MDifferentiableWithinAt.neg {s : Set M} (hf
 : MDiffAt[s] f z) : MDiffAt[s] (-f) z
· 使用定理 `Filter.eventually_of_mem`：eventually_of_mem {f : Filter α} {P : α -> Pro
p} {U : Set α} (hU : U in f) (h : forall x in U, P x) : forallᶠ x in f, P x
· 使用定理 `mem_nhdsWithin_of_mem_nhds`：mem_nhdsWithin_of_mem_nhds {s t : Set α} {a 
: α} (h : s in 𝓝 a) : s in 𝓝[t] a
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Bundle.Trivialization.open_baseSet`：∀ {B : Type u_1} {F : Type u_2} {Z :
 Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 :
 TopologicalSpace Z] {pr…
· 使用定理 `FiberBundle.mem_baseSet_trivializationAt`：mem_baseSet_trivializationAt :
 b in (trivializationAt F E b).baseSet
· 使用定理 `IsLinearMap.map_neg`：map_neg {f : M -> M₂} (lin : IsLinearMap R f) (x : 
M) : f (-x) = -f x
· 使用定理 `Bundle.Trivialization.linear`：∀ (R : Type u_1) {B : Type u_2} {F : Type 
u_3} {E : B → Type u_4} [inst : Semiring R] [inst_1 : TopologicalSpace F]   [ins
t_2 : TopologicalS…
· 使用定理 `trivialization_linear`：∀ (R : Type u_1) {B : Type u_2} {F : Type u_3} {E
 : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x : B) → AddCom
mMonoid (E …
· 使用定理 `instMemTrivializationAtlasTrivializationAt`：∀ {B : Type u_2} {F : Type u
_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {E : B → Type u_5}
   [inst_2 : TopologicalSpace (B…
· 使用定理 `FiberBundle.mem_baseSet_trivializationAt'`：∀ {B : Type u_2} {F : Type u_
3} {inst : TopologicalSpace B} {inst_1 : TopologicalSpace F} {E : B → Type u_5} 
  {inst_2 : TopologicalSpace (B…
-/
lemma mdifferentiableWithinAt_neg_section
    (hs : MDiffAt[u] (T% s) x₀) : MDiffAt[u] (T% (-s)) x₀ := by
  rw [mdifferentiableWithinAt_section] at hs ⊢
  set e := trivializationAt F E x₀
  refine hs.neg.congr_of_eventuallyEq ?_ ?_
  · apply eventually_of_mem (U := e.baseSet)
    · exact mem_nhdsWithin_of_mem_nhds <|
        (e.open_baseSet.mem_nhds <| mem_baseSet_trivializationAt F E x₀)
    · exact fun x hx ↦ (e.linear 𝕜 hx).map_neg ..
  · exact (e.linear 𝕜 (FiberBundle.mem_baseSet_trivializationAt' x₀)).map_neg ..
/-
**mdifferentiableAt_neg_section** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mdifferentiableAt_neg_section (hs : MDiffAt (T% s) x₀) : MDiffAt (T% (-s))
 x₀
参数：hs : MDiffAt (T% s) x₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mdifferentiableWithinAt_univ`：mdifferentiableWithinAt_univ : MDiffAt[uni
v] f x ↔ MDiffAt f x
· 使用引理 `mdifferentiableWithinAt_neg_section`：mdifferentiableWithinAt_neg_section
 (hs : MDiffAt[u] (T% s) x₀) : MDiffAt[u] (T% (-s)) x₀
-/
lemma mdifferentiableAt_neg_section
    (hs : MDiffAt (T% s) x₀) : MDiffAt (T% (-s)) x₀ := by
  rw [← mdifferentiableWithinAt_univ] at hs ⊢
  exact mdifferentiableWithinAt_neg_section hs
/-
**mdifferentiableOn_neg_section** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mdifferentiableOn_neg_section (hs : MDiff[u] (T% s)) : MDiff[u] (T% (-s))
参数：hs : MDiff[u] (T% s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `mdifferentiableWithinAt_neg_section`：mdifferentiableWithinAt_neg_section
 (hs : MDiffAt[u] (T% s) x₀) : MDiffAt[u] (T% (-s)) x₀
-/
lemma mdifferentiableOn_neg_section
    (hs : MDiff[u] (T% s)) : MDiff[u] (T% (-s)) :=
  fun x₀ hx₀ ↦ mdifferentiableWithinAt_neg_section (hs x₀ hx₀)
/-
**mdifferentiable_neg_section** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mdifferentiable_neg_section (hs : MDiff (T% s)) : MDiff (T% (-s))
参数：hs : MDiff (T% s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `mdifferentiableAt_neg_section`：mdifferentiableAt_neg_section (hs : MDiff
At (T% s) x₀) : MDiffAt (T% (-s)) x₀
-/
lemma mdifferentiable_neg_section (hs : MDiff (T% s)) : MDiff (T% (-s)) :=
  fun x₀ ↦ mdifferentiableAt_neg_section (hs x₀)
/-
**mdifferentiableWithinAt_sub_section** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mdifferentiableWithinAt_sub_section (hs : MDiffAt[u] (T% s) x₀) (ht : MDif
fAt[u] (T% t) x₀) : MDiffAt[u] (T% (s - t)) x₀
参数：hs : MDiffAt[u] (T% s) x₀；ht : MDiffAt[u] (T% t) x₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用引理 `mdifferentiableWithinAt_add_section`：mdifferentiableWithinAt_add_section
 (hs : MDiffAt[u] (T% s) x₀) (ht : MDiffAt[u] (T% t) x₀) : MDiffAt[u] (T% (s + t
)) x₀
· 使用引理 `mdifferentiableWithinAt_neg_section`：mdifferentiableWithinAt_neg_section
 (hs : MDiffAt[u] (T% s) x₀) : MDiffAt[u] (T% (-s)) x₀
-/
lemma mdifferentiableWithinAt_sub_section
    (hs : MDiffAt[u] (T% s) x₀) (ht : MDiffAt[u] (T% t) x₀) :
    MDiffAt[u] (T% (s - t)) x₀ := by
  rw [sub_eq_add_neg]
  apply mdifferentiableWithinAt_add_section hs <| mdifferentiableWithinAt_neg_section ht
/-
**mdifferentiableAt_sub_section** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mdifferentiableAt_sub_section (hs : MDiffAt (T% s) x₀) (ht : MDiffAt (T% t
) x₀) : MDiffAt (T% (s - t)) x₀
参数：hs : MDiffAt (T% s) x₀；ht : MDiffAt (T% t) x₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用引理 `mdifferentiableAt_add_section`：mdifferentiableAt_add_section (hs : MDiff
At (T% s) x₀) (ht : MDiffAt (T% t) x₀) : MDiffAt (T% (s + t)) x₀
· 使用引理 `mdifferentiableAt_neg_section`：mdifferentiableAt_neg_section (hs : MDiff
At (T% s) x₀) : MDiffAt (T% (-s)) x₀
-/
lemma mdifferentiableAt_sub_section
    (hs : MDiffAt (T% s) x₀) (ht : MDiffAt (T% t) x₀) :
    MDiffAt (T% (s - t)) x₀ := by
  rw [sub_eq_add_neg]
  apply mdifferentiableAt_add_section hs <| mdifferentiableAt_neg_section ht
/-
**mDifferentiableOn_sub_section** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mDifferentiableOn_sub_section (hs : MDiff[u] (T% s)) (ht : MDiff[u] (T% t)
) : MDiff[u] (T% (s - t))
参数：hs : MDiff[u] (T% s)；ht : MDiff[u] (T% t)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `mdifferentiableWithinAt_sub_section`：mdifferentiableWithinAt_sub_section
 (hs : MDiffAt[u] (T% s) x₀) (ht : MDiffAt[u] (T% t) x₀) : MDiffAt[u] (T% (s - t
)) x₀
-/
lemma mDifferentiableOn_sub_section
    (hs : MDiff[u] (T% s)) (ht : MDiff[u] (T% t)) : MDiff[u] (T% (s - t)) :=
  fun x₀ hx₀ ↦ mdifferentiableWithinAt_sub_section (hs x₀ hx₀) (ht x₀ hx₀)
/-
**mdifferentiable_sub_section** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mdifferentiable_sub_section (hs : MDiff (T% s)) (ht : MDiff (T% t)) : MDif
f (T% (s - t))
参数：hs : MDiff (T% s)；ht : MDiff (T% t)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `mdifferentiableAt_sub_section`：mdifferentiableAt_sub_section (hs : MDiff
At (T% s) x₀) (ht : MDiffAt (T% t) x₀) : MDiffAt (T% (s - t)) x₀
-/
lemma mdifferentiable_sub_section
    (hs : MDiff (T% s)) (ht : MDiff (T% t)) : MDiff (T% (s - t)) :=
  fun x₀ ↦ mdifferentiableAt_sub_section (hs x₀) (ht x₀)
/-
**MDifferentiableWithinAt.smul_section** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MDifferentiableWithinAt.smul_section (hf : MDiffAt[u] f x₀) (hs : MDiffAt[
u] (T% s) x₀) : MDiffAt[u] (T% (f • s)) x₀
参数：hf : MDiffAt[u] f x₀；hs : MDiffAt[u] (T% s) x₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mdifferentiableWithinAt_section`：mdifferentiableWithinAt_section (s : Π 
b, E b) {u : Set B} {b₀ : B} : MDiffAt[u] (T% s) b₀ ↔ MDiffAt[u] (fun b => (triv
ializationAt F E b₀ (…
· 使用定理 `MDifferentiableWithinAt.congr_of_eventuallyEq`：MDifferentiableWithinAt.c
ongr_of_eventuallyEq (h : MDiffAt[s] f x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f 
x) : MDiffAt[s] f₁ x
· 使用定理 `MDifferentiableWithinAt.smul`：MDifferentiableWithinAt.smul (hf : MDiffAt
[s] f x) (hg : MDiffAt[s] g x) : MDiffAt[s] (fun p => f p • g p) x
· 使用定理 `Filter.eventually_of_mem`：eventually_of_mem {f : Filter α} {P : α -> Pro
p} {U : Set α} (hU : U in f) (h : forall x in U, P x) : forallᶠ x in f, P x
· 使用定理 `mem_nhdsWithin_of_mem_nhds`：mem_nhdsWithin_of_mem_nhds {s t : Set α} {a 
: α} (h : s in 𝓝 a) : s in 𝓝[t] a
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Bundle.Trivialization.open_baseSet`：∀ {B : Type u_1} {F : Type u_2} {Z :
 Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 :
 TopologicalSpace Z] {pr…
· 使用定理 `FiberBundle.mem_baseSet_trivializationAt`：mem_baseSet_trivializationAt :
 b in (trivializationAt F E b).baseSet
· 使用定理 `IsLinearMap.map_smul`：∀ {R : Type u} {M : Type v} {M₂ : Type w} [inst : 
Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : AddCommMonoid M₂]   [inst_3 : _
root_.Modu…
· 使用定理 `Bundle.Trivialization.linear`：∀ (R : Type u_1) {B : Type u_2} {F : Type 
u_3} {E : B → Type u_4} [inst : Semiring R] [inst_1 : TopologicalSpace F]   [ins
t_2 : TopologicalS…
· 使用定理 `trivialization_linear`：∀ (R : Type u_1) {B : Type u_2} {F : Type u_3} {E
 : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x : B) → AddCom
mMonoid (E …
· 使用定理 `instMemTrivializationAtlasTrivializationAt`：∀ {B : Type u_2} {F : Type u
_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {E : B → Type u_5}
   [inst_2 : TopologicalSpace (B…
· 使用定理 `FiberBundle.mem_baseSet_trivializationAt'`：∀ {B : Type u_2} {F : Type u_
3} {inst : TopologicalSpace B} {inst_1 : TopologicalSpace F} {E : B → Type u_5} 
  {inst_2 : TopologicalSpace (B…
-/
lemma MDifferentiableWithinAt.smul_section
    (hf : MDiffAt[u] f x₀) (hs : MDiffAt[u] (T% s) x₀) : MDiffAt[u] (T% (f • s)) x₀ := by
  rw [mdifferentiableWithinAt_section] at hs ⊢
  set e := trivializationAt F E x₀
  refine (hf.smul hs).congr_of_eventuallyEq ?_ ?_
  · apply eventually_of_mem (U := e.baseSet)
    · exact mem_nhdsWithin_of_mem_nhds <|
        (e.open_baseSet.mem_nhds <| mem_baseSet_trivializationAt F E x₀)
    · exact fun x hx ↦ (e.linear 𝕜 hx).2 ..
  · apply (e.linear 𝕜 (FiberBundle.mem_baseSet_trivializationAt' x₀)).2
/-
**MDifferentiableAt.smul_section** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MDifferentiableAt.smul_section (hf : MDiffAt f x₀) (hs : MDiffAt (T% s) x₀
) : MDiffAt (T% (f • s)) x₀
参数：hf : MDiffAt f x₀；hs : MDiffAt (T% s) x₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mdifferentiableWithinAt_univ`：mdifferentiableWithinAt_univ : MDiffAt[uni
v] f x ↔ MDiffAt f x
· 使用引理 `MDifferentiableWithinAt.smul_section`：MDifferentiableWithinAt.smul_secti
on (hf : MDiffAt[u] f x₀) (hs : MDiffAt[u] (T% s) x₀) : MDiffAt[u] (T% (f • s)) 
x₀
-/
lemma MDifferentiableAt.smul_section
    (hf : MDiffAt f x₀) (hs : MDiffAt (T% s) x₀) : MDiffAt (T% (f • s)) x₀ := by
  rw [← mdifferentiableWithinAt_univ] at hs ⊢
  exact .smul_section hf hs
/-
**MDifferentiableOn.smul_section** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MDifferentiableOn.smul_section (hf : MDiff[u] f) (hs : MDiff[u] (T% s)) : 
MDiff[u] (T% (f • s))
参数：hf : MDiff[u] f；hs : MDiff[u] (T% s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MDifferentiableWithinAt.smul_section`：MDifferentiableWithinAt.smul_secti
on (hf : MDiffAt[u] f x₀) (hs : MDiffAt[u] (T% s) x₀) : MDiffAt[u] (T% (f • s)) 
x₀
-/
lemma MDifferentiableOn.smul_section
    (hf : MDiff[u] f) (hs : MDiff[u] (T% s)) : MDiff[u] (T% (f • s)) :=
  fun x₀ hx₀ ↦ .smul_section (hf x₀ hx₀) (hs x₀ hx₀)
/-
**mdifferentiable_smul_section** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mdifferentiable_smul_section (hf : MDiff f) (hs : MDiff (T% s)) : MDiff (T
% (f • s))
参数：hf : MDiff f；hs : MDiff (T% s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MDifferentiableAt.smul_section`：MDifferentiableAt.smul_section (hf : MDi
ffAt f x₀) (hs : MDiffAt (T% s) x₀) : MDiffAt (T% (f • s)) x₀
-/
lemma mdifferentiable_smul_section
    (hf : MDiff f) (hs : MDiff (T% s)) : MDiff (T% (f • s)) :=
  fun x₀ ↦ (hf x₀).smul_section (hs x₀)
/-
**mdifferentiableWithinAt_smul_const_section** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mdifferentiableWithinAt_smul_const_section (hs : MDiffAt[u] (T% s) x₀) : M
DiffAt[u] (T% (a • s)) x₀
参数：hs : MDiffAt[u] (T% s) x₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MDifferentiableWithinAt.smul_section`：MDifferentiableWithinAt.smul_secti
on (hf : MDiffAt[u] f x₀) (hs : MDiffAt[u] (T% s) x₀) : MDiffAt[u] (T% (f • s)) 
x₀
· 使用定理 `mdifferentiableWithinAt_const`：mdifferentiableWithinAt_const : MDiffAt[s
] (fun _ : M => c) x
-/
lemma mdifferentiableWithinAt_smul_const_section
    (hs : MDiffAt[u] (T% s) x₀) :
    MDiffAt[u] (T% (a • s)) x₀ :=
  .smul_section mdifferentiableWithinAt_const hs
/-
**MDifferentiableAt.smul_const_section** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MDifferentiableAt.smul_const_section (hs : MDiffAt (T% s) x₀) : MDiffAt (T
% (a • s)) x₀
参数：hs : MDiffAt (T% s) x₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MDifferentiableAt.smul_section`：MDifferentiableAt.smul_section (hf : MDi
ffAt f x₀) (hs : MDiffAt (T% s) x₀) : MDiffAt (T% (f • s)) x₀
· 使用定理 `mdifferentiableAt_const`：mdifferentiableAt_const : MDiffAt (fun _ : M =>
 c) x
-/
lemma MDifferentiableAt.smul_const_section
    (hs : MDiffAt (T% s) x₀) : MDiffAt (T% (a • s)) x₀ :=
  .smul_section mdifferentiableAt_const hs
/-
**MDifferentiableOn.smul_const_section** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MDifferentiableOn.smul_const_section (hs : MDiff[u] (T% s)) : MDiff[u] (T%
 (a • s))
参数：hs : MDiff[u] (T% s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MDifferentiableOn.smul_section`：MDifferentiableOn.smul_section (hf : MDi
ff[u] f) (hs : MDiff[u] (T% s)) : MDiff[u] (T% (f • s))
· 使用定理 `mdifferentiableOn_const`：mdifferentiableOn_const : MDiff[s] (fun _ : M =
> c)
-/
lemma MDifferentiableOn.smul_const_section
    (hs : MDiff[u] (T% s)) : MDiff[u] (T% (a • s)) :=
  .smul_section mdifferentiableOn_const hs
/-
**mdifferentiable_smul_const_section** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mdifferentiable_smul_const_section (hs : MDiff (T% s)) : MDiff (T% (a • s)
)
参数：hs : MDiff (T% s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MDifferentiableAt.smul_const_section`：MDifferentiableAt.smul_const_secti
on (hs : MDiffAt (T% s) x₀) : MDiffAt (T% (a • s)) x₀
-/
lemma mdifferentiable_smul_const_section
    (hs : MDiff (T% s)) : MDiff (T% (a • s)) :=
  fun x₀ ↦ (hs x₀).smul_const_section
/-
**MDifferentiableWithinAt.sum_section** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MDifferentiableWithinAt.sum_section {ι : Type*} {s : Finset ι} {t : ι -> (
x : B) -> E x} (hs : forall i in s, MDiffAt[u] (T% (t i ·)) x₀) : MDiffAt[u] (T%
 (fun x => ∑ i in s, (t i x))) x₀
参数：x : B；hs : forall i in s, MDiffAt[u] (T% (t i ·)) x₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `ContMDiffWithinAt.mdifferentiableWithinAt`：ContMDiffWithinAt.mdifferenti
ableWithinAt (hf : CMDiffAt[s] n f x) (hn : n != 0) : MDiffAt[s] f x
· 使用定理 `Bundle.contMDiffWithinAt_zeroSection`：contMDiffWithinAt_zeroSection {t :
 Set B} {x : B} : ContMDiffWithinAt IB (IB.prod 𝓘(𝕜, F)) n (zeroSection F E) t x
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用引理 `mdifferentiableWithinAt_add_section`：mdifferentiableWithinAt_add_section
 (hs : MDiffAt[u] (T% s) x₀) (ht : MDiffAt[u] (T% t) x₀) : MDiffAt[u] (T% (s + t
)) x₀
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma MDifferentiableWithinAt.sum_section {ι : Type*} {s : Finset ι} {t : ι → (x : B) → E x}
    (hs : ∀ i ∈ s, MDiffAt[u] (T% (t i ·)) x₀) :
    MDiffAt[u] (T% (fun x ↦ ∑ i ∈ s, (t i x))) x₀ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using! (contMDiffWithinAt_zeroSection 𝕜 E).mdifferentiableWithinAt one_ne_zero
  | insert i s hi h =>
    simp only [Finset.mem_insert, forall_eq_or_imp] at hs
    simpa [Finset.sum_insert hi] using mdifferentiableWithinAt_add_section (hs.1) (h hs.2)
/-
**MDifferentiableAt.sum_section** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MDifferentiableAt.sum_section {ι : Type*} {s : Finset ι} {t : ι -> (x : B)
 -> E x} {x₀ : B} (hs : forall i in s, MDiffAt (T% (t i ·)) x₀) : MDiffAt (T% (f
un x => ∑ i in s, (t i x))) x₀
参数：x : B；hs : forall i in s, MDiffAt (T% (t i ·)) x₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MDifferentiableWithinAt.sum_section`：MDifferentiableWithinAt.sum_section
 {ι : Type*} {s : Finset ι} {t : ι -> (x : B) -> E x} (hs : forall i in s, MDiff
At[u] (T% (t i ·)) x₀) : …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
lemma MDifferentiableAt.sum_section {ι : Type*} {s : Finset ι} {t : ι → (x : B) → E x} {x₀ : B}
    (hs : ∀ i ∈ s, MDiffAt (T% (t i ·)) x₀) :
    MDiffAt (T% (fun x ↦ ∑ i ∈ s, (t i x))) x₀ := by
  simp_rw [← mdifferentiableWithinAt_univ] at hs ⊢
  exact MDifferentiableWithinAt.sum_section hs
/-
**MDifferentiableOn.sum_section** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MDifferentiableOn.sum_section {ι : Type*} {s : Finset ι} {t : ι -> (x : B)
 -> E x} (hs : forall i in s, MDiff[u] (T% (t i ·))) : MDiff[u] (T% (fun x => ∑ 
i in s, (t i x)))
参数：x : B；hs : forall i in s, MDiff[u] (T% (t i ·))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MDifferentiableWithinAt.sum_section`：MDifferentiableWithinAt.sum_section
 {ι : Type*} {s : Finset ι} {t : ι -> (x : B) -> E x} (hs : forall i in s, MDiff
At[u] (T% (t i ·)) x₀) : …
-/
lemma MDifferentiableOn.sum_section {ι : Type*} {s : Finset ι} {t : ι → (x : B) → E x}
    (hs : ∀ i ∈ s, MDiff[u] (T% (t i ·))) :
    MDiff[u] (T% (fun x ↦ ∑ i ∈ s, (t i x))) :=
  fun x₀ hx₀ ↦ .sum_section fun i hi ↦ hs i hi x₀ hx₀
/-
**MDifferentiable.sum_section** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MDifferentiable.sum_section {ι : Type*} {s : Finset ι} {t : ι -> (x : B) -
> E x} (hs : forall i in s, MDiff (T% (t i ·))) : MDiff (T% (fun x => ∑ i in s, 
(t i x)))
参数：x : B；hs : forall i in s, MDiff (T% (t i ·))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MDifferentiableAt.sum_section`：MDifferentiableAt.sum_section {ι : Type*}
 {s : Finset ι} {t : ι -> (x : B) -> E x} {x₀ : B} (hs : forall i in s, MDiffAt 
(T% (t i ·)) x₀) : …
-/
lemma MDifferentiable.sum_section {ι : Type*} {s : Finset ι} {t : ι → (x : B) → E x}
    (hs : ∀ i ∈ s, MDiff (T% (t i ·))) :
    MDiff (T% (fun x ↦ ∑ i ∈ s, (t i x))) :=
  fun x₀ ↦ .sum_section fun i hi ↦ (hs i) hi x₀

/-- The scalar product `ψ • s` of a differentiable function `ψ : M → 𝕜` and a section `s` of a
vector bundle `V → M` is differentiable once `s` is differentiable on an open set containing
`tsupport ψ`.

See `ContMDiffOn.smul_section_of_tsupport` for the analogous result about `C^n` sections. -/
/-
**MDifferentiableOn.smul_section_of_tsupport** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MDifferentiableOn.smul_section_of_tsupport {s : Π (x : B), E x} {ψ : B -> 
𝕜} (hψ : MDiff[u] ψ) (ht : IsOpen u) (ht' : tsupport ψ subseteq u) (hs : MDiff[u
] (T% s)) : MDiff (T% (ψ • s))
参数：x : B；hψ : MDiff[u] ψ；ht : IsOpen u；ht' : tsupport ψ subseteq u；hs : MDiff[u]
 (T% s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `mdifferentiable_of_mdifferentiableOn_union_of_isOpen`：mdifferentiable_of
_mdifferentiableOn_union_of_isOpen (hf : MDiff[s] f) (hf' : MDiff[t] f) (hst : s
 union t = univ) (hs : IsOpen s) (ht : IsO…
· 使用引理 `MDifferentiableOn.smul_section`：MDifferentiableOn.smul_section (hf : MDi
ff[u] f) (hs : MDiff[u] (T% s)) : MDiff[u] (T% (f • s))
· 使用定理 `MDifferentiableOn.congr`：MDifferentiableOn.congr (h : MDiff[s] f) (h₁ : 
forall y in s, f₁ y = f y) : MDiff[s] f₁
· 使用定理 `MDifferentiable.mdifferentiableOn`：MDifferentiable.mdifferentiableOn (h 
: MDiff f) : MDiff[s] f
· 使用定理 `Bundle.mdifferentiable_zeroSection`：mdifferentiable_zeroSection : MDiff 
(zeroSection F E)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `image_eq_zero_of_notMem_tsupport`：∀ {X : Type u_1} {α : Type u_2} [inst 
: Zero α] [inst_1 : TopologicalSpace X] {f : X → α} {x : X},   x ∉ tsupport f → 
f x = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.compl_subset_iff_union`：compl_subset_iff_union {s t : Set α} : sᶜ su
bseteq t ↔ s union t = univ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.compl_subset_compl`：compl_subset_compl : sᶜ subseteq tᶜ ↔ t subseteq
 s
· 使用定理 `isOpen_compl_iff`：∀ {X : Type u} {s : Set X} [inst : TopologicalSpace X]
, IsOpen sᶜ ↔ IsClosed s
· 使用定理 `isClosed_tsupport`：∀ {X : Type u_1} {α : Type u_2} [inst : Zero α] [inst
_1 : TopologicalSpace X] (f : X → α), IsClosed (tsupport f)

--- 原说明 ---
The scalar product `ψ • s` of a differentiable function `ψ : M → 𝕜` and a sectio
n `s` of a
vector bundle `V → M` is differentiable once `s` is differentiable on an open se
t containing
`tsupport ψ`.

See `ContMDiffOn.smul_section_of_tsupport` for the analogous result about `C^n` 
sections.
-/
lemma MDifferentiableOn.smul_section_of_tsupport {s : Π (x : B), E x} {ψ : B → 𝕜}
    (hψ : MDiff[u] ψ) (ht : IsOpen u) (ht' : tsupport ψ ⊆ u) (hs : MDiff[u] (T% s)) :
    MDiff (T% (ψ • s)) := by
  apply mdifferentiable_of_mdifferentiableOn_union_of_isOpen (hψ.smul_section hs) ?_ ?_ ht
      (isOpen_compl_iff.mpr <| isClosed_tsupport ψ)
  · apply ((mdifferentiable_zeroSection _ _).mdifferentiableOn (s := (tsupport ψ)ᶜ)).congr
    intro y hy
    simp [image_eq_zero_of_notMem_tsupport hy, zeroSection]
  · exact Set.compl_subset_iff_union.mp <| Set.compl_subset_compl.mpr ht'

variable {ι : Type*} {t : ι → (x : B) → E x}

open Function

/-- The sum of a locally finite collection of sections is differentiable if each section is.
Version at a point within a set. -/
/-
**MDifferentiableWithinAt.sum_section_of_locallyFinite** 是 Mathlib 中的一个引理，位于命名空间
 ``。
形式化陈述：MDifferentiableWithinAt.sum_section_of_locallyFinite (ht : LocallyFinite f
un i => {x : B | t i x != 0}) (ht' : forall i, MDiffAt[u] (T% (t i ·)) x₀) : MDi
ffAt[u] (T% (fun x => ∑' i, (t i x))) x₀
参数：ht : LocallyFinite fun i => {x : B | t i x != 0}；ht' : forall i, MDiffAt[u] (
T% (t i ·)) x₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MDifferentiableWithinAt.sum_section`：MDifferentiableWithinAt.sum_section
 {ι : Type*} {s : Finset ι} {t : ι -> (x : B) -> E x} (hs : forall i in s, MDiff
At[u] (T% (t i ·)) x₀) : …
· 使用定理 `MDifferentiableWithinAt.mono`：MDifferentiableWithinAt.mono (hst : s subs
eteq t) (h : MDiffAt[t] f x) : MDiffAt[s] f x
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mdifferentiableWithinAt_inter`：mdifferentiableWithinAt_inter (ht : t in 
𝓝 x) : MDiffAt[s inter t] f x ↔ MDiffAt[s] f x
· 使用定理 `MDifferentiableWithinAt.congr'`：MDifferentiableWithinAt.congr' (h : MDif
fAt[s] f x) (ht : forall x in t, f₁ x = f x) (hst : s subseteq t) (hxt : x in t)
 : MDiffAt[s] f₁ x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.TotalSpace.mk_inj`：∀ {B : Type u_1} {F : Type u_2} {E : B → Type 
u_3} {b : B} {y y' : E b}, ⟨b, y⟩ = ⟨b, y'⟩ ↔ y = y'
· 使用定理 `tsum_eq_sum'`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [
inst_1 : TopologicalSpace α] {f : β → α}   {L : SummationFilter β} [L.LeAtTop] {
s …
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.support_subset_iff'`：∀ {ι : Type u_1} {M : Type u_3} [inst : Ze
ro M] {f : ι → M} {s : Set ι}, Function.support f ⊆ s ↔ ∀ x ∉ s, f x = 0
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Set.mem_toFinset`：mem_toFinset {s : Set α} [Fintype s] {a : α} : a in s.
toFinset ↔ a in s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s

--- 原说明 ---
The sum of a locally finite collection of sections is differentiable if each sec
tion is.
Version at a point within a set.
-/
lemma MDifferentiableWithinAt.sum_section_of_locallyFinite
    (ht : LocallyFinite fun i ↦ {x : B | t i x ≠ 0})
    (ht' : ∀ i, MDiffAt[u] (T% (t i ·)) x₀) :
    MDiffAt[u] (T% (fun x ↦ ∑' i, (t i x))) x₀ := by
  obtain ⟨u', hu', hfin⟩ := ht x₀
  -- All sections `t i` but a finite set `s` vanish near `x₀`: choose a neighbourhood `u` of `x₀`
  -- and a finite set `s` of sections which don't vanish.
  let s := {i | ((fun i ↦ {x | t i x ≠ 0}) i ∩ u').Nonempty}
  have := hfin.fintype
  have : MDiffAt[u ∩ u'] (T% (fun x ↦ ∑ i ∈ s, (t i x))) x₀ :=
     .sum_section fun i _ ↦ ((ht' i).mono inter_subset_left)
  apply (mdifferentiableWithinAt_inter hu').mp
  apply this.congr' (fun y hy ↦ ?_) inter_subset_right (mem_of_mem_nhds hu')
  rw [TotalSpace.mk_inj, tsum_eq_sum']
  refine support_subset_iff'.mpr fun i hi ↦ ?_
  by_contra! h
  have : i ∈ s.toFinset := by
    refine Set.mem_toFinset.mpr ?_
    simp only [s, ne_eq, Set.mem_ofPred_eq]
    use y
    simp [h, hy]
  exact hi this

/-- The sum of a locally finite collection of sections is differentiable at `x`
if each section is. -/
/-
**MDifferentiableAt.sum_section_of_locallyFinite** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MDifferentiableAt.sum_section_of_locallyFinite (ht : LocallyFinite fun i =
> {x : B | t i x != 0}) (ht' : forall i, MDiffAt (T% (t i ·)) x₀) : MDiffAt (T% 
(fun x => ∑' i, (t i x))) x₀
参数：ht : LocallyFinite fun i => {x : B | t i x != 0}；ht' : forall i, MDiffAt (T% 
(t i ·)) x₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MDifferentiableWithinAt.sum_section_of_locallyFinite`：MDifferentiableWit
hinAt.sum_section_of_locallyFinite (ht : LocallyFinite fun i => {x : B | t i x !
= 0}) (ht' : forall i, MDiffAt[u] (T% (t i…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a

--- 原说明 ---
The sum of a locally finite collection of sections is differentiable at `x`
if each section is.
-/
lemma MDifferentiableAt.sum_section_of_locallyFinite
    (ht : LocallyFinite fun i ↦ {x : B | t i x ≠ 0})
    (ht' : ∀ i, MDiffAt (T% (t i ·)) x₀) :
    MDiffAt (T% (fun x ↦ ∑' i, (t i x))) x₀ := by
  simp_rw [← mdifferentiableWithinAt_univ] at ht' ⊢
  exact .sum_section_of_locallyFinite ht ht'

/-- The sum of a locally finite collection of sections is differentiable on a set `u`
if each section is. -/
/-
**MDifferentiableOn.sum_section_of_locallyFinite** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MDifferentiableOn.sum_section_of_locallyFinite (ht : LocallyFinite fun i =
> {x : B | t i x != 0}) (ht' : forall i, MDiff[u] (T% (t i ·))) : MDiff[u] (T% (
fun x => ∑' i, (t i x)))
参数：ht : LocallyFinite fun i => {x : B | t i x != 0}；ht' : forall i, MDiff[u] (T%
 (t i ·))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MDifferentiableWithinAt.sum_section_of_locallyFinite`：MDifferentiableWit
hinAt.sum_section_of_locallyFinite (ht : LocallyFinite fun i => {x : B | t i x !
= 0}) (ht' : forall i, MDiffAt[u] (T% (t i…

--- 原说明 ---
The sum of a locally finite collection of sections is differentiable on a set `u
`
if each section is.
-/
lemma MDifferentiableOn.sum_section_of_locallyFinite
    (ht : LocallyFinite fun i ↦ {x : B | t i x ≠ 0})
    (ht' : ∀ i, MDiff[u] (T% (t i ·))) :
    MDiff[u] (T% (fun x ↦ ∑' i, (t i x))) :=
  fun x hx ↦ .sum_section_of_locallyFinite ht (ht' · x hx)

/-- The sum of a locally finite collection of sections is differentiable if each section is. -/
/-
**MDifferentiable.sum_section_of_locallyFinite** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MDifferentiable.sum_section_of_locallyFinite (ht : LocallyFinite fun i => 
{x : B | t i x != 0}) (ht' : forall i, MDiff (T% (t i ·))) : MDiff (T% (fun x =>
 ∑' i, (t i x)))
参数：ht : LocallyFinite fun i => {x : B | t i x != 0}；ht' : forall i, MDiff (T% (t
 i ·))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MDifferentiableAt.sum_section_of_locallyFinite`：MDifferentiableAt.sum_se
ction_of_locallyFinite (ht : LocallyFinite fun i => {x : B | t i x != 0}) (ht' :
 forall i, MDiffAt (T% (t i ·)) x₀) …

--- 原说明 ---
The sum of a locally finite collection of sections is differentiable if each sec
tion is.
-/
lemma MDifferentiable.sum_section_of_locallyFinite (ht : LocallyFinite fun i ↦ {x : B | t i x ≠ 0})
    (ht' : ∀ i, MDiff (T% (t i ·))) :
    MDiff (T% (fun x ↦ ∑' i, (t i x))) :=
  fun x ↦ .sum_section_of_locallyFinite ht fun i ↦ ht' i x
/-
**MDifferentiableWithinAt.finsum_section_of_locallyFinite** 是 Mathlib 中的一个引理，位于命
名空间 ``。
形式化陈述：MDifferentiableWithinAt.finsum_section_of_locallyFinite (ht : LocallyFinit
e fun i => {x : B | t i x != 0}) (ht' : forall i, MDiffAt[u] (T% (t i ·)) x₀) : 
MDiffAt[u] (T% (fun x => ∑ᶠ i, t i x)) x₀
参数：ht : LocallyFinite fun i => {x : B | t i x != 0}；ht' : forall i, MDiffAt[u] (
T% (t i ·)) x₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableWithinAt.congr'`：MDifferentiableWithinAt.congr' (h : MDif
fAt[s] f x) (ht : forall x in t, f₁ x = f x) (hst : s subseteq t) (hxt : x in t)
 : MDiffAt[s] f₁ x
· 使用引理 `MDifferentiableWithinAt.sum_section_of_locallyFinite`：MDifferentiableWit
hinAt.sum_section_of_locallyFinite (ht : LocallyFinite fun i => {x : B | t i x !
= 0}) (ht' : forall i, MDiffAt[u] (T% (t i…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `tsum_eq_finsum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {f : β → α}   {L : SummationFilter β} [L.LeAtTop]
, Fu…
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `trivial`：True
-/
lemma MDifferentiableWithinAt.finsum_section_of_locallyFinite
    (ht : LocallyFinite fun i ↦ {x : B | t i x ≠ 0})
    (ht' : ∀ i, MDiffAt[u] (T% (t i ·)) x₀) :
    MDiffAt[u] (T% (fun x ↦ ∑ᶠ i, t i x)) x₀ := by
  apply (MDifferentiableWithinAt.sum_section_of_locallyFinite ht ht').congr' (t := Set.univ)
      (fun y hy ↦ ?_) (by grind) trivial
  choose U hu hfin using ht y
  have : {x | t x y ≠ 0} ⊆ {i | ((fun i ↦ {x | t i x ≠ 0}) i ∩ U).Nonempty} := by
    intro x hx
    rw [Set.mem_ofPred] at hx ⊢
    use y
    simpa using ⟨hx, mem_of_mem_nhds hu⟩
  rw [tsum_eq_finsum (hfin.subset this)]
/-
**MDifferentiableAt.finsum_section_of_locallyFinite** 是 Mathlib 中的一个引理，位于命名空间 ``
。
形式化陈述：MDifferentiableAt.finsum_section_of_locallyFinite (ht : LocallyFinite fun 
i => {x : B | t i x != 0}) (ht' : forall i, MDiffAt (T% (t i ·)) x₀) : MDiffAt (
T% (fun x => ∑ᶠ i, t i x)) x₀
参数：ht : LocallyFinite fun i => {x : B | t i x != 0}；ht' : forall i, MDiffAt (T% 
(t i ·)) x₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MDifferentiableWithinAt.finsum_section_of_locallyFinite`：MDifferentiable
WithinAt.finsum_section_of_locallyFinite (ht : LocallyFinite fun i => {x : B | t
 i x != 0}) (ht' : forall i, MDiffAt[u] (T% (…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
lemma MDifferentiableAt.finsum_section_of_locallyFinite
    (ht : LocallyFinite fun i ↦ {x : B | t i x ≠ 0})
    (ht' : ∀ i, MDiffAt (T% (t i ·)) x₀) :
    MDiffAt (T% (fun x ↦ ∑ᶠ i, t i x)) x₀ := by
  simp_rw [← mdifferentiableWithinAt_univ] at ht' ⊢
  exact .finsum_section_of_locallyFinite ht ht'
/-
**MDifferentiableOn.finsum_section_of_locallyFinite** 是 Mathlib 中的一个引理，位于命名空间 ``
。
形式化陈述：MDifferentiableOn.finsum_section_of_locallyFinite (ht : LocallyFinite fun 
i => {x : B | t i x != 0}) (ht' : forall i, MDiff[u] (T% (t i ·))) : MDiff[u] (T
% (fun x => ∑ᶠ i, t i x))
参数：ht : LocallyFinite fun i => {x : B | t i x != 0}；ht' : forall i, MDiff[u] (T%
 (t i ·))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MDifferentiableWithinAt.finsum_section_of_locallyFinite`：MDifferentiable
WithinAt.finsum_section_of_locallyFinite (ht : LocallyFinite fun i => {x : B | t
 i x != 0}) (ht' : forall i, MDiffAt[u] (T% (…
-/
lemma MDifferentiableOn.finsum_section_of_locallyFinite
    (ht : LocallyFinite fun i ↦ {x : B | t i x ≠ 0}) (ht' : ∀ i, MDiff[u] (T% (t i ·))) :
    MDiff[u] (T% (fun x ↦ ∑ᶠ i, t i x)) :=
  fun x hx ↦ .finsum_section_of_locallyFinite ht fun i ↦ ht' i x hx
/-
**MDifferentiable.finsum_section_of_locallyFinite** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MDifferentiable.finsum_section_of_locallyFinite (ht : LocallyFinite fun i 
=> {x : B | t i x != 0}) (ht' : forall i, MDiff (T% (t i ·))) : MDiff (T% (fun x
 => ∑ᶠ i, t i x))
参数：ht : LocallyFinite fun i => {x : B | t i x != 0}；ht' : forall i, MDiff (T% (t
 i ·))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MDifferentiableAt.finsum_section_of_locallyFinite`：MDifferentiableAt.fin
sum_section_of_locallyFinite (ht : LocallyFinite fun i => {x : B | t i x != 0}) 
(ht' : forall i, MDiffAt (T% (t i ·)) x…
-/
lemma MDifferentiable.finsum_section_of_locallyFinite
    (ht : LocallyFinite fun i ↦ {x : B | t i x ≠ 0}) (ht' : ∀ i, MDiff (T% (t i ·))) :
    MDiff (T% (fun x ↦ ∑ᶠ i, t i x)) :=
  fun x ↦ .finsum_section_of_locallyFinite ht fun i ↦ ht' i x

end operations

section

/- Declare two manifolds `B₁` and `B₂` (with models `IB₁ : HB₁ → EB₁` and `IB₂ : HB₂ → EB₂`),
and two vector bundles `E₁` and `E₂` respectively over `B₁` and `B₂` (with model fibers
`F₁` and `F₂`).

Also a third manifold `M`, which will be the source of all our maps.
-/
variable {𝕜 F₁ F₂ B₁ B₂ M : Type*} {E₁ : B₁ → Type*} {E₂ : B₂ → Type*} [NontriviallyNormedField 𝕜]
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)] [∀ x, AddCommGroup (E₂ x)]
  [∀ x, Module 𝕜 (E₂ x)] [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  {EB₁ : Type*}
  [NormedAddCommGroup EB₁] [NormedSpace 𝕜 EB₁] {HB₁ : Type*} [TopologicalSpace HB₁]
  {IB₁ : ModelWithCorners 𝕜 EB₁ HB₁} [TopologicalSpace B₁] [ChartedSpace HB₁ B₁]
  {EB₂ : Type*}
  [NormedAddCommGroup EB₂] [NormedSpace 𝕜 EB₂] {HB₂ : Type*} [TopologicalSpace HB₂]
  {IB₂ : ModelWithCorners 𝕜 EB₂ HB₂} [TopologicalSpace B₂] [ChartedSpace HB₂ B₂]
  {EM : Type*}
  [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  {n : ℕ∞} [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  {b₁ : M → B₁} {b₂ : M → B₂} {m₀ : M}
  {ϕ : Π (m : M), E₁ (b₁ m) →L[𝕜] E₂ (b₂ m)} {v : Π (m : M), E₁ (b₁ m)} {s : Set M}

/-- Consider a differentiable map `v : M → E₁` to a vector bundle, over a basemap `b₁ : M → B₁`, and
another basemap `b₂ : M → B₂`. Given linear maps `ϕ m : E₁ (b₁ m) → E₂ (b₂ m)` depending
differentiably on `m`, one can apply `ϕ m` to `g m`, and the resulting map is differentiable.

Note that the differentiability of `ϕ` cannot be always be stated as differentiability of a map
into a manifold, as the pullback bundles `b₁ *ᵖ E₁` and `b₂ *ᵖ E₂` only make sense when `b₁`
and `b₂` are globally smooth, but we want to apply this lemma with only local information.
Therefore, we formulate it using differentiability of `ϕ` read in coordinates.

Version for `MDifferentiableWithinAt`. We also give a version for `MDifferentiableAt`, but no
version for `MDifferentiableOn` or `MDifferentiable` as our assumption, written in coordinates,
only makes sense around a point.
-/
/-
**MDifferentiableWithinAt.clm_apply_of_inCoordinates** 是 Mathlib 中的一个引理，位于命名空间 `
`。
形式化陈述：MDifferentiableWithinAt.clm_apply_of_inCoordinates (hϕ : MDiffAt[s] (fun m
 => inCoordinates F₁ E₁ F₂ E₂ (b₁ m₀) (b₁ m) (b₂ m₀) (b₂ m) (ϕ m)) m₀) (hv : MDi
ffAt[s] (fun m => (v m : TotalSpace F₁ E₁)) m₀) (hb₂ : MDiffAt[s] b₂ m₀) : MDiff
At[s] (fun m => (ϕ m (v m) : TotalSpace F₂ E₂)) m₀
参数：hϕ : MDiffAt[s] (fun m => inCoordinates F₁ E₁ F₂ E₂ (b₁ m₀) (b₁ m) (b₂ m₀) (b
₂ m) (ϕ m)) m₀；hv : MDiffAt[s] (fun m => (v m : TotalSpace F₁ E₁)) m₀；hb₂ : MDif
fAt[s] b₂ m₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mdifferentiableWithinAt_totalSpace`：mdifferentiableWithinAt_totalSpace (
f : M -> TotalSpace F E) {s : Set M} {x₀ : M} : MDiffAt[s] f x₀ ↔ MDiffAt[s] (fu
n x => (f x).proj) x₀ ∧ …
· 使用定理 `MDifferentiableWithinAt.congr_of_eventuallyEq_insert`：MDifferentiableWit
hinAt.congr_of_eventuallyEq_insert (h : MDiffAt[s] f x) (h₁ : f₁ =ᶠ[𝓝[insert x s
] x] f) : MDiffAt[s] f₁ x
· 使用定理 `MDifferentiableWithinAt.clm_apply`：MDifferentiableWithinAt.clm_apply {g 
: M -> F₁ ->L[𝕜] F₂} {f : M -> F₁} {s : Set M} {x : M} (hg : MDiffAt[s] g x) (hf
 : MDiffAt[s] f x) : MD…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MDifferentiableWithinAt.continuousWithinAt`：MDifferentiableWithinAt.cont
inuousWithinAt {f : M -> M'} {s : Set M} {x : M} (hf : MDifferentiableWithinAt I
 I' f s x) : ContinuousWithinAt …
· 使用定理 `MDifferentiableWithinAt.insert`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 E] {H : Type u_…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Bundle.Trivialization.open_baseSet`：∀ {B : Type u_1} {F : Type u_2} {Z :
 Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 :
 TopologicalSpace Z] {pr…
· 使用定理 `FiberBundle.mem_baseSet_trivializationAt'`：∀ {B : Type u_2} {F : Type u_
3} {inst : TopologicalSpace B} {inst_1 : TopologicalSpace F} {E : B → Type u_5} 
  {inst_2 : TopologicalSpace (B…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `trivialization_linear`：∀ (R : Type u_1) {B : Type u_2} {F : Type u_3} {E
 : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x : B) → AddCom
mMonoid (E …
· 使用定理 `instMemTrivializationAtlasTrivializationAt`：∀ {B : Type u_2} {F : Type u
_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {E : B → Type u_5}
   [inst_2 : TopologicalSpace (B…
· 使用定理 `ContinuousLinearMap.inCoordinates_eq`：∀ {B : Type u_2} {F : Type u_3} {E
 : B → Type u_4} [inst : (x : B) → AddCommMonoid (E x)]   [inst_1 : NormedAddCom
mGroup F] [inst_2 : Topolo…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Bundle.Trivialization.continuousLinearEquivAt_symm_apply`：∀ (R : Type u_
1) {B : Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : NontriviallyNormedFi
eld R]   [inst_1 : (x : B) → AddCommMonoid (E …
· 使用定理 `Bundle.Trivialization.symm_apply_apply_mk`：∀ {B : Type u_1} {F : Type u_
2} {E : B → Type u_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] 
  [inst_2 : TopologicalSpace (B…
· 使用定理 `Bundle.Trivialization.continuousLinearEquivAt_apply`：∀ (R : Type u_1) {B
 : Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : NontriviallyNormedField R
]   [inst_1 : (x : B) → AddCommMonoid (E …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Consider a differentiable map `v : M → E₁` to a vector bundle, over a basemap `b
₁ : M → B₁`, and
another basemap `b₂ : M → B₂`. Given linear maps `ϕ m : E₁ (b₁ m) → E₂ (b₂ m)` d
epending
differentiably on `m`, one can apply `ϕ m` to `g m`, and the resulting map is di
fferentiable.

Note that the differentiability of `ϕ` cannot be always be stated as differentia
bility of a map
into a manifold, as the pullback bundles `b₁ *ᵖ E₁` and `b₂ *ᵖ E₂` only make sen
se when `b₁`
and `b₂` are globally smooth, but we want to apply this lemma with only local in
formation.
Therefore, we formulate it using differentiability of `ϕ` read in coordinates.

Version for `MDifferentiableWithinAt`. We also give a version for `MDifferentiab
leAt`, but no
version for `MDifferentiableOn` or `MDifferentiable` as our assumption, written 
in coordinates,
only makes sense around a point.
-/
lemma MDifferentiableWithinAt.clm_apply_of_inCoordinates
    (hϕ : MDiffAt[s] (fun m ↦ inCoordinates F₁ E₁ F₂ E₂ (b₁ m₀) (b₁ m) (b₂ m₀) (b₂ m) (ϕ m)) m₀)
    (hv : MDiffAt[s] (fun m ↦ (v m : TotalSpace F₁ E₁)) m₀)
    (hb₂ : MDiffAt[s] b₂ m₀) :
    MDiffAt[s] (fun m ↦ (ϕ m (v m) : TotalSpace F₂ E₂)) m₀ := by
  rw [mdifferentiableWithinAt_totalSpace] at hv ⊢
  refine ⟨hb₂, ?_⟩
  apply (MDifferentiableWithinAt.clm_apply hϕ hv.2).congr_of_eventuallyEq_insert
  have A : ∀ᶠ m in 𝓝[insert m₀ s] m₀, b₁ m ∈ (trivializationAt F₁ E₁ (b₁ m₀)).baseSet := by
    apply hv.1.insert.continuousWithinAt
    apply (trivializationAt F₁ E₁ (b₁ m₀)).open_baseSet.mem_nhds
    exact FiberBundle.mem_baseSet_trivializationAt' (b₁ m₀)
  have A' : ∀ᶠ m in 𝓝[insert m₀ s] m₀, b₂ m ∈ (trivializationAt F₂ E₂ (b₂ m₀)).baseSet := by
    apply hb₂.insert.continuousWithinAt
    apply (trivializationAt F₂ E₂ (b₂ m₀)).open_baseSet.mem_nhds
    exact FiberBundle.mem_baseSet_trivializationAt' (b₂ m₀)
  filter_upwards [A, A'] with m hm h'm
  rw [inCoordinates_eq hm h'm]
  simp [hm]

/-- Consider a differentiable map `v : M → E₁` to a vector bundle, over a basemap `b₁ : M → B₁`, and
another basemap `b₂ : M → B₂`. Given linear maps `ϕ m : E₁ (b₁ m) → E₂ (b₂ m)` depending
differentiably on `m`, one can apply `ϕ m` to `g m`, and the resulting map is differentiable.

Note that the differentiability of `ϕ` cannot be always be stated as differentiability of a map
into a manifold, as the pullback bundles `b₁ *ᵖ E₁` and `b₂ *ᵖ E₂` only make sense when `b₁`
and `b₂` are globally smooth, but we want to apply this lemma with only local information.
Therefore, we formulate it using differentiability of `ϕ` read in coordinates.

Version for `MDifferentiableAt`. We also give a version for `MDifferentiableWithinAt`,
but no version for `MDifferentiableOn` or `MDifferentiable` as our assumption, written
in coordinates, only makes sense around a point.
-/
/-
**MDifferentiableAt.clm_apply_of_inCoordinates** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MDifferentiableAt.clm_apply_of_inCoordinates (hϕ : MDiffAt (fun m => inCoo
rdinates F₁ E₁ F₂ E₂ (b₁ m₀) (b₁ m) (b₂ m₀) (b₂ m) (ϕ m)) m₀) (hv : MDiffAt (fun
 m => (v m : TotalSpace F₁ E₁)) m₀) (hb₂ : MDiffAt b₂ m₀) : MDiffAt (fun m => (ϕ
 m (v m) : TotalSpace F₂ E₂)) m₀
参数：hϕ : MDiffAt (fun m => inCoordinates F₁ E₁ F₂ E₂ (b₁ m₀) (b₁ m) (b₂ m₀) (b₂ m
) (ϕ m)) m₀；hv : MDiffAt (fun m => (v m : TotalSpace F₁ E₁)) m₀；hb₂ : MDiffAt b₂
 m₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mdifferentiableWithinAt_univ`：mdifferentiableWithinAt_univ : MDiffAt[uni
v] f x ↔ MDiffAt f x
· 使用引理 `MDifferentiableWithinAt.clm_apply_of_inCoordinates`：MDifferentiableWithi
nAt.clm_apply_of_inCoordinates (hϕ : MDiffAt[s] (fun m => inCoordinates F₁ E₁ F₂
 E₂ (b₁ m₀) (b₁ m) (b₂ m₀) (b₂ m) (ϕ m))…

--- 原说明 ---
Consider a differentiable map `v : M → E₁` to a vector bundle, over a basemap `b
₁ : M → B₁`, and
another basemap `b₂ : M → B₂`. Given linear maps `ϕ m : E₁ (b₁ m) → E₂ (b₂ m)` d
epending
differentiably on `m`, one can apply `ϕ m` to `g m`, and the resulting map is di
fferentiable.

Note that the differentiability of `ϕ` cannot be always be stated as differentia
bility of a map
into a manifold, as the pullback bundles `b₁ *ᵖ E₁` and `b₂ *ᵖ E₂` only make sen
se when `b₁`
and `b₂` are globally smooth, but we want to apply this lemma with only local in
formation.
Therefore, we formulate it using differentiability of `ϕ` read in coordinates.

Version for `MDifferentiableAt`. We also give a version for `MDifferentiableWith
inAt`,
but no version for `MDifferentiableOn` or `MDifferentiable` as our assumption, w
ritten
in coordinates, only makes sense around a point.
-/
lemma MDifferentiableAt.clm_apply_of_inCoordinates
    (hϕ : MDiffAt (fun m ↦ inCoordinates F₁ E₁ F₂ E₂ (b₁ m₀) (b₁ m) (b₂ m₀) (b₂ m) (ϕ m)) m₀)
    (hv : MDiffAt (fun m ↦ (v m : TotalSpace F₁ E₁)) m₀) (hb₂ : MDiffAt b₂ m₀) :
    MDiffAt (fun m ↦ (ϕ m (v m) : TotalSpace F₂ E₂)) m₀ := by
  rw [← mdifferentiableWithinAt_univ] at hϕ hv hb₂ ⊢
  exact MDifferentiableWithinAt.clm_apply_of_inCoordinates hϕ hv hb₂

end

section extend

namespace FiberBundle
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  (F : Type*) [NormedAddCommGroup F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [(x : M) → AddCommGroup (V x)]
  [(x : M) → TopologicalSpace (V x)]
  [FiberBundle F V] [NormedSpace 𝕜 F] {k : WithTop ℕ∞}

/-
**FiberBundle.exists_contMDiffOn_extend** 是 Mathlib 中的一个引理，位于命名空间 `FiberBundle`。
形式化陈述：exists_contMDiffOn_extend [(x : M) -> Module 𝕜 (V x)] [VectorBundle 𝕜 F V]
 [ContMDiffVectorBundle k F V I] {x₀ : M} (σ₀ : V x₀) : exists s in 𝓝 x₀, CMDiff
[s] k (T% (extend F σ₀))
参数：x : M；V x；σ₀ : V x₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Bundle.Trivialization.open_baseSet`：∀ {B : Type u_1} {F : Type u_2} {Z :
 Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 :
 TopologicalSpace Z] {pr…
· 使用定理 `FiberBundle.mem_baseSet_trivializationAt'`：∀ {B : Type u_2} {F : Type u_
3} {inst : TopologicalSpace B} {inst_1 : TopologicalSpace F} {E : B → Type u_5} 
  {inst_2 : TopologicalSpace (B…
· 使用定理 `contMDiffOn_const`：contMDiffOn_const : ContMDiffOn I I' n (fun _ : M => 
c) s
· 使用定理 `ContMDiffOn.congr`：ContMDiffOn.congr (h : ContMDiffOn I I' n f s) (h₁ : 
forall y in s, f₁ y = f y) : ContMDiffOn I I' n f₁ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.Trivialization.apply_mk_symm`：∀ {B : Type u_1} {F : Type u_2} {E 
: B → Type u_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [ins
t_2 : TopologicalSpace (B…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Bundle.Trivialization.contMDiffWithinAt_section`：contMDiffWithinAt_secti
on {s : forall x, E x} (a : Set B) {x₀ : B} {e : Trivialization F (Bundle.TotalS
pace.proj : Bundle.TotalSpace F E -> …
· 使用定理 `instMemTrivializationAtlasTrivializationAt`：∀ {B : Type u_2} {F : Type u
_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {E : B → Type u_5}
   [inst_2 : TopologicalSpace (B…
-/
lemma exists_contMDiffOn_extend [(x : M) → Module 𝕜 (V x)] [VectorBundle 𝕜 F V]
    [ContMDiffVectorBundle k F V I] {x₀ : M} (σ₀ : V x₀) :
    ∃ s ∈ 𝓝 x₀, CMDiff[s] k (T% (extend F σ₀)) := by
  set t := trivializationAt F V x₀
  refine ⟨t.baseSet, ?_, ?_⟩
  · refine t.open_baseSet.mem_nhds ?_
    exact FiberBundle.mem_baseSet_trivializationAt' x₀
  suffices CMDiff[t.baseSet] k (fun x ↦ (t ⟨x, extend F σ₀ x⟩).2) by
    intro x hx
    rw [t.contMDiffWithinAt_section _ hx]
    exact this x hx
  let w : F := (t ⟨x₀, σ₀⟩).2
  have : CMDiff[t.baseSet] k (fun (_x : M) ↦ w) := contMDiffOn_const
  exact this.congr (fun x hx ↦ by simp [extend, t, w, hx])
/-
**FiberBundle.contMDiffAt_extend** 是 Mathlib 中的一个引理，位于命名空间 `FiberBundle`。
形式化陈述：contMDiffAt_extend {x : M} (σ₀ : V x) : CMDiffAt k (T% (extend F σ₀)) x
参数：σ₀ : V x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.contMDiffAt_section`：contMDiffAt_section {s : forall x, E x} (x₀ 
: B) : ContMDiffAt IB (IB.prod 𝓘(𝕜, F)) n (fun x => TotalSpace.mk' F x (s x)) x₀
 ↔ ContMDiffAt I…
· 使用定理 `contMDiffAt_const`：contMDiffAt_const : ContMDiffAt I I' n (fun _ : M => 
c) x
· 使用定理 `ContMDiffAt.congr_of_eventuallyEq`：ContMDiffAt.congr_of_eventuallyEq (h 
: ContMDiffAt I I' n f x) (h₁ : f₁ =ᶠ[𝓝 x] f) : ContMDiffAt I I' n f₁ x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eventually_nhds_iff`：eventually_nhds_iff {p : X -> Prop} : (forallᶠ y in
 𝓝 x, p y) ↔ exists t : Set X, (forall y in t, p y) ∧ IsOpen t ∧ x in t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Bundle.Trivialization.apply_mk_symm`：∀ {B : Type u_1} {F : Type u_2} {E 
: B → Type u_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [ins
t_2 : TopologicalSpace (B…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Bundle.Trivialization.open_baseSet`：∀ {B : Type u_1} {F : Type u_2} {Z :
 Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 :
 TopologicalSpace Z] {pr…
· 使用定理 `FiberBundle.mem_baseSet_trivializationAt'`：∀ {B : Type u_2} {F : Type u_
3} {inst : TopologicalSpace B} {inst_1 : TopologicalSpace F} {E : B → Type u_5} 
  {inst_2 : TopologicalSpace (B…
-/
lemma contMDiffAt_extend {x : M} (σ₀ : V x) : CMDiffAt k (T% (extend F σ₀)) x := by
  rw [contMDiffAt_section]
  set t := trivializationAt F V x
  let w : F := (t ⟨x, σ₀⟩).2
  have : CMDiffAt k (fun (_x : M) ↦ w) x := contMDiffAt_const
  refine this.congr_of_eventuallyEq ?_
  apply eventually_nhds_iff.mpr
  refine ⟨t.baseSet, ?_, t.open_baseSet, ?_⟩
  · intro x hx
    simp [extend, t, hx, w]
  · exact FiberBundle.mem_baseSet_trivializationAt' x

@[deprecated (since := "2026-06-30")] alias contMDiffAt_extend' := contMDiffAt_extend
/-
**FiberBundle.exists_mdifferentiableOn_extend** 是 Mathlib 中的一个引理，位于命名空间 `FiberBu
ndle`。
形式化陈述：exists_mdifferentiableOn_extend [forall x, Module 𝕜 (V x)] [VectorBundle 𝕜
 F V] [ContMDiffVectorBundle 1 F V I] {x₀ : M} (σ₀ : V x₀) : exists s in 𝓝 x₀, M
Diff[s] (T% (extend F σ₀))
参数：V x；σ₀ : V x₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `FiberBundle.exists_contMDiffOn_extend`：exists_contMDiffOn_extend [(x : M
) -> Module 𝕜 (V x)] [VectorBundle 𝕜 F V] [ContMDiffVectorBundle k F V I] {x₀ : 
M} (σ₀ : V x₀) : exists s i…
· 使用定理 `ContMDiffOn.mdifferentiableOn`：ContMDiffOn.mdifferentiableOn (hf : CMDif
f[s] n f) (hn : n != 0) : MDiff[s] f
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
-/
lemma exists_mdifferentiableOn_extend [∀ x, Module 𝕜 (V x)] [VectorBundle 𝕜 F V]
    [ContMDiffVectorBundle 1 F V I] {x₀ : M} (σ₀ : V x₀) :
    ∃ s ∈ 𝓝 x₀, MDiff[s] (T% (extend F σ₀)) := by
  obtain ⟨s, hs, hsσ⟩ := exists_contMDiffOn_extend (k := 1) I F σ₀
  exact ⟨s, hs, hsσ.mdifferentiableOn one_ne_zero⟩
/-
**FiberBundle.mdifferentiableAt_extend** 是 Mathlib 中的一个引理，位于命名空间 `FiberBundle`。
形式化陈述：mdifferentiableAt_extend {x : M} (σ₀ : V x) : MDiffAt (T% (extend F σ₀)) x
参数：σ₀ : V x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffAt.mdifferentiableAt`：ContMDiffAt.mdifferentiableAt (hf : CMDif
fAt n f x) (hn : n != 0) : MDiffAt f x
· 使用引理 `FiberBundle.contMDiffAt_extend`：contMDiffAt_extend {x : M} (σ₀ : V x) : 
CMDiffAt k (T% (extend F σ₀)) x
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
-/
lemma mdifferentiableAt_extend {x : M} (σ₀ : V x) :
    MDiffAt (T% (extend F σ₀)) x :=
  (contMDiffAt_extend (k := 1) I F σ₀).mdifferentiableAt one_ne_zero

variable (V) in
/-
**FiberBundle._root_.VectorBundle.injective_eval_mdifferentiableAt_sec** 是 Mathl
ib 中的一个引理，位于命名空间 `FiberBundle`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.VectorBundle.injective_eval_mdifferentiableAt_sec [∀ x, Module 𝕜 (V x)]
    (W : Type*) [AddCommGroup W] [Module 𝕜 W] [TopologicalSpace W] (x : M) :
    Function.Injective
      (fun A : V x →L[𝕜] W ↦
        fun (Z : Π x, V x) (_ : MDiffAt (T% Z) x) ↦ A (Z x)) := by
  intro X X' h
  ext σ₀
  simpa using congr($h (extend F σ₀) (mdifferentiableAt_extend ..))

variable (V) in
/-
**FiberBundle._root_.VectorBundle.injective_eval_contMDiffAt_sec** 是 Mathlib 中的一
个引理，位于命名空间 `FiberBundle`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.VectorBundle.injective_eval_contMDiffAt_sec {n : WithTop ℕ∞} [∀ x, Module 𝕜 (V x)]
    (W : Type*) [AddCommGroup W] [Module 𝕜 W] [TopologicalSpace W] (x : M) :
    Function.Injective
      (fun A : V x →L[𝕜] W ↦
        fun (Z : Π x, V x) (_ : CMDiffAt n (T% Z) x) ↦ A (Z x)) := by
  intro X X' h
  ext σ₀
  simpa using congr($h (extend F σ₀) (contMDiffAt_extend ..))

end FiberBundle
end extend

