/-
Copyright (c) 2022 Floris van Doorn, Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Heather Macbeth
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.VectorBundle.FiberwiseLinear
public import Mathlib.Topology.VectorBundle.Constructions

/-! # `C^n` vector bundles

This file defines `C^n` vector bundles over a manifold.

Let `E` be a topological vector bundle, with model fiber `F` and base space `B`.  We consider `E` as
carrying a charted space structure given by its trivializations -- these are charts to `B × F`.
Then, by "composition", if `B` is itself a charted space over `H` (e.g. a smooth manifold), then `E`
is also a charted space over `H × F`.

Now, we define `ContMDiffVectorBundle` as the `Prop` of having `C^n` transition functions.
Recall the structure groupoid `contMDiffFiberwiseLinear` on `B × F` consisting of `C^n`, fiberwise
linear open partial homeomorphisms.  We show that our definition of "`C^n` vector bundle" implies
`HasGroupoid` for this groupoid, and show (by a "composition" of `HasGroupoid` instances) that
this means that a `C^n` vector bundle is a `C^n` manifold.

Since `ContMDiffVectorBundle` is a mixin, it should be easy to make variants and for many such
variants to coexist -- vector bundles can be `C^n` vector bundles over several different base
fields, etc.

## Main definitions and constructions

* `FiberBundle.chartedSpace`: A fiber bundle `E` over a base `B` with model fiber `F` is naturally
  a charted space modelled on `B × F`.

* `FiberBundle.chartedSpace'`: Let `B` be a charted space modelled on `HB`.  Then a fiber bundle
  `E` over a base `B` with model fiber `F` is naturally a charted space modelled on `HB.prod F`.

* `ContMDiffVectorBundle`: Mixin class stating that a (topological) `VectorBundle` is `C^n`, in the
  sense of having `C^n` transition functions, where the smoothness index `n`
  belongs to `ℕ∞ω` (notation for `WithTop ℕ∞` in the `ContDiff` scope).

* `ContMDiffFiberwiseLinear.hasGroupoid`: For a `C^n` vector bundle `E` over `B` with fiber
  modelled on `F`, the change-of-co-ordinates between two trivializations `e`, `e'` for `E`,
  considered as charts to `B × F`, is `C^n` and fiberwise linear, in the sense of belonging to the
  structure groupoid `contMDiffFiberwiseLinear`.

* `Bundle.TotalSpace.isManifold`: A `C^n` vector bundle is naturally a `C^n` manifold.

* `VectorBundleCore.instContMDiffVectorBundle`: If a (topological) `VectorBundleCore` is `C^n`,
  in the sense of having `C^n` transition functions (cf. `VectorBundleCore.IsContMDiff`),
  then the vector bundle constructed from it is a `C^n` vector bundle.

* `VectorPrebundle.contMDiffVectorBundle`: If a `VectorPrebundle` is `C^n`,
  in the sense of having `C^n` transition functions (cf. `VectorPrebundle.IsContMDiff`),
  then the vector bundle constructed from it is a `C^n` vector bundle.

* `Bundle.Prod.contMDiffVectorBundle`: The direct sum of two `C^n` vector bundles is a `C^n`
  vector bundle.
-/

@[expose] public section

assert_not_exists mfderiv

open Bundle Set OpenPartialHomeomorph

open Function (id_def)

open Filter

open scoped Manifold Bundle Topology ContDiff

variable {n : ℕ∞ω} {𝕜 B B' F M : Type*} {E : B → Type*}

/-! ### Charted space structure on a fiber bundle -/


section

variable [TopologicalSpace F] [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)]
  {HB : Type*} [TopologicalSpace HB] [TopologicalSpace B] [ChartedSpace HB B] [FiberBundle F E]

/-- A fiber bundle `E` over a base `B` with model fiber `F` is naturally a charted space modelled on
`B × F`. -/
/-
**FiberBundle.chartedSpace'** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：FiberBundle.chartedSpace' : ChartedSpace (B × F) (TotalSpace F E) where at
las
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A fiber bundle `E` over a base `B` with model fiber `F` is naturally a charted s
pace modelled on
`B × F`.
-/
instance FiberBundle.chartedSpace' : ChartedSpace (B × F) (TotalSpace F E) where
  atlas :=
    (fun e : Trivialization F (π F E) => e.toOpenPartialHomeomorph) '' trivializationAtlas F E
  chartAt x := (trivializationAt F E x.proj).toOpenPartialHomeomorph
  mem_chart_source x :=
    (trivializationAt F E x.proj).mem_source.mpr (mem_baseSet_trivializationAt F E x.proj)
  chart_mem_atlas _ := mem_image_of_mem _ (trivialization_mem_atlas F E _)
/-
**FiberBundle.chartedSpace'_chartAt** 是 Mathlib 中的一个定理，位于命名空间 `FiberBundle`。
形式化陈述：∀ {B : Type u_2} {F : Type u_4} {E : B → Type u_6} [inst : TopologicalSpac
e F]   [inst_1 : TopologicalSpace (Bundle.TotalSpace F E)] [inst_2 : (x : B) → T
opologicalSpace (E x)]   [inst_3 : TopologicalSpace B] [inst_4 : FiberBundle F E
] (x : Bundle.TotalSpace F E),   chartAt (B × F) x = (trivializationAt F E x.pro
j).toOpenPartialHomeomorph
参数：Bundle.TotalSpace F E；x : B；E x；x : Bundle.TotalSpace F E；B × F；trivializatio
nAt F E x.proj。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem FiberBundle.chartedSpace'_chartAt (x : TotalSpace F E) :
    chartAt (B × F) x = (trivializationAt F E x.proj).toOpenPartialHomeomorph :=
  rfl

/- Porting note: In Lean 3, the next instance was inside a section with locally reducible
`ModelProd` and it used `ModelProd B F` as the intermediate space. Using `B × F` in the middle
gives the same instance.
-/
--attribute [local reducible] ModelProd

/-- Let `B` be a charted space modelled on `HB`.  Then a fiber bundle `E` over a base `B` with model
fiber `F` is naturally a charted space modelled on `HB.prod F`. -/
/-
**FiberBundle.chartedSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：FiberBundle.chartedSpace : ChartedSpace (ModelProd HB F) (TotalSpace F E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `B` be a charted space modelled on `HB`.  Then a fiber bundle `E` over a bas
e `B` with model
fiber `F` is naturally a charted space modelled on `HB.prod F`.
-/
instance FiberBundle.chartedSpace : ChartedSpace (ModelProd HB F) (TotalSpace F E) :=
  ChartedSpace.comp _ (B × F) _

set_option backward.isDefEq.respectTransparency false in
/-
**FiberBundle.chartedSpace_chartAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：FiberBundle.chartedSpace_chartAt (x : TotalSpace F E) : chartAt (ModelProd
 HB F) x = (trivializationAt F E x.proj).toOpenPartialHomeomorph ≫ₕ (chartAt HB 
x.proj).prod (OpenPartialHomeomorph.refl F)
参数：x : TotalSpace F E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.Trivialization.coe_coe`：∀ {B : Type u_1} {F : Type u_2} {Z : Type
 u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z → B}  
 [inst_2 : Topologi…
· 使用定理 `Bundle.Trivialization.coe_fst'`：∀ {B : Type u_1} {F : Type u_2} {Z : Typ
e u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z → B} 
  [inst_2 : Topologi…
· 使用定理 `FiberBundle.mem_baseSet_trivializationAt`：mem_baseSet_trivializationAt :
 b in (trivializationAt F E b).baseSet
-/
theorem FiberBundle.chartedSpace_chartAt (x : TotalSpace F E) :
    chartAt (ModelProd HB F) x =
      (trivializationAt F E x.proj).toOpenPartialHomeomorph ≫ₕ
        (chartAt HB x.proj).prod (OpenPartialHomeomorph.refl F) := by
  dsimp only [chartAt_comp, prodChartedSpace_chartAt, FiberBundle.chartedSpace'_chartAt,
    chartAt_self_eq]
  rw [Trivialization.coe_coe, Trivialization.coe_fst' _ (mem_baseSet_trivializationAt F E x.proj)]
/-
**FiberBundle.chartedSpace_chartAt_symm_fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：FiberBundle.chartedSpace_chartAt_symm_fst (x : TotalSpace F E) (y : ModelP
rod HB F) (hy : y in (chartAt (ModelProd HB F) x).target) : ((chartAt (ModelProd
 HB F) x).symm y).proj = (chartAt HB x.proj).symm y.1
参数：x : TotalSpace F E；y : ModelProd HB F；hy : y in (chartAt (ModelProd HB F) x).
target。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FiberBundle.chartedSpace_chartAt`：FiberBundle.chartedSpace_chartAt (x : 
TotalSpace F E) : chartAt (ModelProd HB F) x = (trivializationAt F E x.proj).toO
penPartialHomeomorph ≫…
· 使用定理 `Bundle.Trivialization.proj_symm_apply`：∀ {B : Type u_1} {F : Type u_2} {
Z : Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : 
Z → B}   [inst_2 : Topologi…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `OpenPartialHomeomorph.prod_toPartialHomeomorph`：∀ {X : Type u_1} {X' : T
ype u_2} {Y : Type u_3} {Y' : Type u_4} [inst : TopologicalSpace X]   [inst_1 : 
TopologicalSpace X'] [inst_2 : Topol…
-/
theorem FiberBundle.chartedSpace_chartAt_symm_fst (x : TotalSpace F E) (y : ModelProd HB F)
    (hy : y ∈ (chartAt (ModelProd HB F) x).target) :
    ((chartAt (ModelProd HB F) x).symm y).proj = (chartAt HB x.proj).symm y.1 := by
  simp only [FiberBundle.chartedSpace_chartAt, mfld_simps] at hy ⊢
  exact (trivializationAt F E x.proj).proj_symm_apply hy.2

end

section

variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)] {EB : Type*}
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} (E' : B → Type*) [∀ x, Zero (E' x)] {EM : Type*}
  [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M] [ChartedSpace HM M]

variable [TopologicalSpace B] [ChartedSpace HB B] [FiberBundle F E]

set_option backward.isDefEq.respectTransparency false in
/-
**FiberBundle.extChartAt** 是 Mathlib 中的一个定理，位于命名空间 `FiberBundle`。
形式化陈述：∀ {𝕜 : Type u_1} {B : Type u_2} {F : Type u_4} {E : B → Type u_6} [inst : 
NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup F] [inst_2 : NormedSpa
ce 𝕜 F] [inst_3 : TopologicalSpace (Bundle.TotalSpace F E)]   [inst_4 : (x : B) 
→ TopologicalSpace (E x)] {EB : Type u_7} [inst_5 : NormedAddCommGroup EB]   [in
st_6 : NormedSpace 𝕜 EB] {HB : Type u_8} [inst_7 : TopologicalSpace HB] {IB : Mo
delWithCorners 𝕜 EB HB}   [inst_8 : TopologicalSpace B] [inst_9 : ChartedSpace H
B B] [inst_10 : FiberBundle F E] (x : Bundle.TotalSpace F E),   extChartAt (IB.p
rod (modelWithCornersSelf 𝕜 F)) x =     (trivializationAt F E x.proj).trans ((ex
tChartAt IB x.proj).prod (PartialEquiv.refl F))
参数：Bundle.TotalSpace F E；x : B；E x；x : Bundle.TotalSpace F E；IB.prod (modelWithC
ornersSelf 𝕜 F)；trivializationAt F E x.proj；(extChartAt IB x.proj).prod (Partial
Equiv.refl F)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FiberBundle.chartedSpace_chartAt`：FiberBundle.chartedSpace_chartAt (x : 
TotalSpace F E) : chartAt (ModelProd HB F) x = (trivializationAt F E x.proj).toO
penPartialHomeomorph ≫…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `OpenPartialHomeomorph.prod_toPartialHomeomorph`：∀ {X : Type u_1} {X' : T
ype u_2} {Y : Type u_3} {Y' : Type u_4} [inst : TopologicalSpace X]   [inst_1 : 
TopologicalSpace X'] [inst_2 : Topol…
· 使用定理 `PartialEquiv.trans_assoc`：trans_assoc (e'' : PartialEquiv γ δ) : (e.tran
s e').trans e'' = e.trans (e'.trans e'')
· 使用定理 `PartialEquiv.prod_trans`：prod_trans {η : Type*} {ε : Type*} (e : Partial
Equiv α β) (f : PartialEquiv β γ) (e' : PartialEquiv δ η) (f' : PartialEquiv η ε
) : (e.prod e…
· 使用定理 `PartialEquiv.refl_trans`：refl_trans : (PartialEquiv.refl α).trans e = e
-/
protected theorem FiberBundle.extChartAt (x : TotalSpace F E) :
    extChartAt (IB.prod 𝓘(𝕜, F)) x =
      (trivializationAt F E x.proj).toPartialEquiv ≫
        (extChartAt IB x.proj).prod (PartialEquiv.refl F) := by
  simp_rw [extChartAt, FiberBundle.chartedSpace_chartAt, OpenPartialHomeomorph.extend]
  simp only [PartialEquiv.trans_assoc, mfld_simps]
  -- Porting note: should not be needed
  rw [PartialEquiv.prod_trans, PartialEquiv.refl_trans]
/-
**FiberBundle.extChartAt_target** 是 Mathlib 中的一个定理，位于命名空间 `FiberBundle`。
形式化陈述：∀ {𝕜 : Type u_1} {B : Type u_2} {F : Type u_4} {E : B → Type u_6} [inst : 
NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup F] [inst_2 : NormedSpa
ce 𝕜 F] [inst_3 : TopologicalSpace (Bundle.TotalSpace F E)]   [inst_4 : (x : B) 
→ TopologicalSpace (E x)] {EB : Type u_7} [inst_5 : NormedAddCommGroup EB]   [in
st_6 : NormedSpace 𝕜 EB] {HB : Type u_8} [inst_7 : TopologicalSpace HB] {IB : Mo
delWithCorners 𝕜 EB HB}   [inst_8 : TopologicalSpace B] [inst_9 : ChartedSpace H
B B] [inst_10 : FiberBundle F E] (x : Bundle.TotalSpace F E),   (extChartAt (IB.
prod (modelWithCornersSelf 𝕜 F)) x).target =     ((extChartAt IB x.proj).target 
∩ ↑(extChartAt IB x.proj).symm ⁻¹' (trivializationAt F E x.proj).baseSet) ×ˢ Set
.univ
参数：Bundle.TotalSpace F E；x : B；E x；x : Bundle.TotalSpace F E；extChartAt (IB.prod
 (modelWithCornersSelf 𝕜 F)) x；(extChartAt IB x.proj).target ∩ ↑(extChartAt IB x
.proj).symm ⁻¹' (trivializationAt F E x.proj).baseSet。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FiberBundle.extChartAt`：∀ {𝕜 : Type u_1} {B : Type u_2} {F : Type u_4} {
E : B → Type u_6} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGr
oup F] [inst…
· 使用定理 `PartialEquiv.trans_target`：trans_target : (e.trans e').target = e'.targe
t inter e'.symm ⁻¹' e.target
· 使用定理 `Bundle.Trivialization.target_eq`：∀ {B : Type u_1} {F : Type u_2} {Z : Ty
pe u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 : To
pologicalSpace Z] {pr…
· 使用定理 `Set.inter_prod`：inter_prod : (s₁ inter s₂) ×ˢ t = s₁ ×ˢ t inter s₂ ×ˢ t
-/
protected theorem FiberBundle.extChartAt_target (x : TotalSpace F E) :
    (extChartAt (IB.prod 𝓘(𝕜, F)) x).target =
      ((extChartAt IB x.proj).target ∩
        (extChartAt IB x.proj).symm ⁻¹' (trivializationAt F E x.proj).baseSet) ×ˢ univ := by
  rw [FiberBundle.extChartAt, PartialEquiv.trans_target, Trivialization.target_eq, inter_prod]
  rfl
/-
**FiberBundle.writtenInExtChartAt_trivializationAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：FiberBundle.writtenInExtChartAt_trivializationAt {x : TotalSpace F E} {y} 
(hy : y in (extChartAt (IB.prod 𝓘(𝕜, F)) x).target) : writtenInExtChartAt (IB.pr
od 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) x (trivializationAt F E x.proj) y = y
参数：hy : y in (extChartAt (IB.prod 𝓘(𝕜, F)) x).target。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `writtenInExtChartAt_chartAt_comp`：writtenInExtChartAt_chartAt_comp [Char
tedSpace H H'] (x : M') {y} (hy : y in letI
-/
theorem FiberBundle.writtenInExtChartAt_trivializationAt {x : TotalSpace F E} {y}
    (hy : y ∈ (extChartAt (IB.prod 𝓘(𝕜, F)) x).target) :
    writtenInExtChartAt (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) x
      (trivializationAt F E x.proj) y = y :=
  writtenInExtChartAt_chartAt_comp _ hy
/-
**FiberBundle.writtenInExtChartAt_trivializationAt_symm** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：FiberBundle.writtenInExtChartAt_trivializationAt_symm {x : TotalSpace F E}
 {y} (hy : y in (extChartAt (IB.prod 𝓘(𝕜, F)) x).target) : writtenInExtChartAt (
IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) (trivializationAt F E x.proj x) (trivializati
onAt F E x.proj).toOpenPartialHomeomorph.symm y = y
参数：hy : y in (extChartAt (IB.prod 𝓘(𝕜, F)) x).target。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `writtenInExtChartAt_chartAt_symm_comp`：writtenInExtChartAt_chartAt_symm_
comp [ChartedSpace H H'] (x : M') {y} (hy : y in letI
-/
theorem FiberBundle.writtenInExtChartAt_trivializationAt_symm {x : TotalSpace F E} {y}
    (hy : y ∈ (extChartAt (IB.prod 𝓘(𝕜, F)) x).target) :
    writtenInExtChartAt (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) (trivializationAt F E x.proj x)
      (trivializationAt F E x.proj).toOpenPartialHomeomorph.symm y = y :=
  writtenInExtChartAt_chartAt_symm_comp _ hy

/-! ### Regularity of maps in/out fiber bundles

Note: For these results we don't need that the bundle is a `C^n` vector bundle, or even a vector
bundle at all, just that it is a fiber bundle over a charted base space.
-/

namespace Bundle

/-- Characterization of `C^n` functions into a vector bundle.
Version at a point within a set. -/
/-
**Bundle.contMDiffWithinAt_totalSpace** 是 Mathlib 中的一个定理，位于命名空间 `Bundle`。
形式化陈述：contMDiffWithinAt_totalSpace {f : M -> TotalSpace F E} {s : Set M} {x₀ : M
} : ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F)) n f s x₀ ↔ ContMDiffWithinAt IM IB n 
(fun x => (f x).proj) s x₀ ∧ ContMDiffWithinAt IM 𝓘(𝕜, F) n (fun x => (trivializ
ationAt F E (f x₀).proj (f x)).2) s x₀
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
· 使用定理 `contMDiffWithinAt_prod_iff`：contMDiffWithinAt_prod_iff (f : M -> M' × N'
) : ContMDiffWithinAt I (I'.prod J') n f s x ↔ ContMDiffWithinAt I I' n (Prod.fs
t ∘ f) s x ∧ Con…
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
· 使用定理 `Filter.EventuallyEq.contMDiffWithinAt_iff`：Filter.EventuallyEq.contMDiff
WithinAt_iff (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : ContMDiffWithinAt I I' n
 f₁ s x ↔ ContMDiffWithinAt I I…
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
Characterization of `C^n` functions into a vector bundle.
Version at a point within a set.
-/
theorem contMDiffWithinAt_totalSpace {f : M → TotalSpace F E} {s : Set M} {x₀ : M} :
    ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F)) n f s x₀ ↔
      ContMDiffWithinAt IM IB n (fun x => (f x).proj) s x₀ ∧
      ContMDiffWithinAt IM 𝓘(𝕜, F) n (fun x ↦ (trivializationAt F E (f x₀).proj (f x)).2) s x₀ := by
  simp +singlePass only [contMDiffWithinAt_iff_target]
  rw [and_and_and_comm, ← FiberBundle.continuousWithinAt_totalSpace, and_congr_right_iff]
  intro hf
  simp_rw +instances [modelWithCornersSelf_prod, FiberBundle.extChartAt, Function.comp_def,
    PartialEquiv.trans_apply, PartialEquiv.prod_coe, PartialEquiv.refl_coe,
    extChartAt_self_apply, modelWithCornersSelf_coe, Function.id_def, ← chartedSpaceSelf_prod]
  refine (contMDiffWithinAt_prod_iff _).trans (and_congr ?_ Iff.rfl)
  have h1 : (fun x => (f x).proj) ⁻¹' (trivializationAt F E (f x₀).proj).baseSet ∈ 𝓝[s] x₀ :=
    ((FiberBundle.continuous_proj F E).continuousWithinAt.comp hf (mapsTo_image f s))
      ((Trivialization.open_baseSet _).mem_nhds (mem_baseSet_trivializationAt F E _))
  refine EventuallyEq.contMDiffWithinAt_iff (eventually_of_mem h1 fun x hx => ?_) ?_
  · simp_rw [Function.comp, OpenPartialHomeomorph.coe_toPartialEquiv, Trivialization.coe_coe]
    rw [Trivialization.coe_fst']
    exact hx
  · simp only [mfld_simps]

/-- Characterization of `C^n` functions into a vector bundle. Version at a point. -/
/-
**Bundle.contMDiffAt_totalSpace** 是 Mathlib 中的一个定理，位于命名空间 `Bundle`。
形式化陈述：contMDiffAt_totalSpace {f : M -> TotalSpace F E} {x₀ : M} : ContMDiffAt IM
 (IB.prod 𝓘(𝕜, F)) n f x₀ ↔ ContMDiffAt IM IB n (fun x => (f x).proj) x₀ ∧ ContM
DiffAt IM 𝓘(𝕜, F) n (fun x => (trivializationAt F E (f x₀).proj (f x)).2) x₀
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.contMDiffWithinAt_totalSpace`：contMDiffWithinAt_totalSpace {f : M
 -> TotalSpace F E} {s : Set M} {x₀ : M} : ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F)
) n f s x₀ ↔ ContMDiffWit…

--- 原说明 ---
Characterization of `C^n` functions into a vector bundle. Version at a point.
-/
theorem contMDiffAt_totalSpace {f : M → TotalSpace F E} {x₀ : M} :
    ContMDiffAt IM (IB.prod 𝓘(𝕜, F)) n f x₀ ↔
      ContMDiffAt IM IB n (fun x ↦ (f x).proj) x₀ ∧
        ContMDiffAt IM 𝓘(𝕜, F) n (fun x ↦ (trivializationAt F E (f x₀).proj (f x)).2) x₀ := by
  simp_rw [← contMDiffWithinAt_univ]; exact contMDiffWithinAt_totalSpace

/-- Characterization of `C^n` sections within a set at a point of a vector bundle. -/
/-
**Bundle.contMDiffWithinAt_section** 是 Mathlib 中的一个定理，位于命名空间 `Bundle`。
形式化陈述：contMDiffWithinAt_section {s : forall x, E x} {a : Set B} {x₀ : B} : ContM
DiffWithinAt IB (IB.prod 𝓘(𝕜, F)) n (fun x => TotalSpace.mk' F x (s x)) a x₀ ↔ C
ontMDiffWithinAt IB 𝓘(𝕜, F) n (fun x => (trivializationAt F E x₀ ⟨x, s x⟩).2) a 
x₀
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `contMDiffWithinAt_id`：contMDiffWithinAt_id : ContMDiffWithinAt I I n (id
 : M -> M) s x

--- 原说明 ---
Characterization of `C^n` sections within a set at a point of a vector bundle.
-/
theorem contMDiffWithinAt_section {s : ∀ x, E x} {a : Set B} {x₀ : B} :
    ContMDiffWithinAt IB (IB.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (s x)) a x₀ ↔
      ContMDiffWithinAt IB 𝓘(𝕜, F) n (fun x ↦ (trivializationAt F E x₀ ⟨x, s x⟩).2) a x₀ := by
  simp_rw [contMDiffWithinAt_totalSpace, and_iff_right_iff_imp]; intro; exact contMDiffWithinAt_id

/-- Characterization of `C^n` sections of a vector bundle. -/
/-
**Bundle.contMDiffAt_section** 是 Mathlib 中的一个定理，位于命名空间 `Bundle`。
形式化陈述：contMDiffAt_section {s : forall x, E x} (x₀ : B) : ContMDiffAt IB (IB.prod
 𝓘(𝕜, F)) n (fun x => TotalSpace.mk' F x (s x)) x₀ ↔ ContMDiffAt IB 𝓘(𝕜, F) n (f
un x => (trivializationAt F E x₀ ⟨x, s x⟩).2) x₀
参数：x₀ : B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `contMDiffAt_id`：contMDiffAt_id : ContMDiffAt I I n (id : M -> M) x

--- 原说明 ---
Characterization of `C^n` sections of a vector bundle.
-/
theorem contMDiffAt_section {s : ∀ x, E x} (x₀ : B) :
    ContMDiffAt IB (IB.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (s x)) x₀ ↔
      ContMDiffAt IB 𝓘(𝕜, F) n (fun x ↦ (trivializationAt F E x₀ ⟨x, s x⟩).2) x₀ := by
  simp_rw [contMDiffAt_totalSpace, and_iff_right_iff_imp]; intro; exact contMDiffAt_id

variable (E)
/-
**Bundle.contMDiff_proj** 是 Mathlib 中的一个定理，位于命名空间 `Bundle`。
形式化陈述：contMDiff_proj : ContMDiff (IB.prod 𝓘(𝕜, F)) IB n (π F E)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contMDiffAt_id`：contMDiffAt_id : ContMDiffAt I I n (id : M -> M) x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.contMDiffAt_totalSpace`：contMDiffAt_totalSpace {f : M -> TotalSpa
ce F E} {x₀ : M} : ContMDiffAt IM (IB.prod 𝓘(𝕜, F)) n f x₀ ↔ ContMDiffAt IM IB n
 (fun x => (f x).pr…
-/
theorem contMDiff_proj : ContMDiff (IB.prod 𝓘(𝕜, F)) IB n (π F E) := fun x ↦ by
  have : ContMDiffAt (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) n id x := contMDiffAt_id
  rw [contMDiffAt_totalSpace] at this
  exact this.1
/-
**Bundle.contMDiffOn_proj** 是 Mathlib 中的一个定理，位于命名空间 `Bundle`。
形式化陈述：contMDiffOn_proj {s : Set (TotalSpace F E)} : ContMDiffOn (IB.prod 𝓘(𝕜, F)
) IB n (π F E) s
参数：TotalSpace F E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiff.contMDiffOn`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
H : Type u_…
· 使用定理 `Bundle.contMDiff_proj`：contMDiff_proj : ContMDiff (IB.prod 𝓘(𝕜, F)) IB n
 (π F E)
-/
theorem contMDiffOn_proj {s : Set (TotalSpace F E)} :
    ContMDiffOn (IB.prod 𝓘(𝕜, F)) IB n (π F E) s :=
  (contMDiff_proj E).contMDiffOn
/-
**Bundle.contMDiffAt_proj** 是 Mathlib 中的一个定理，位于命名空间 `Bundle`。
形式化陈述：contMDiffAt_proj {p : TotalSpace F E} : ContMDiffAt (IB.prod 𝓘(𝕜, F)) IB n
 (π F E) p
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiff.contMDiffAt`：ContMDiff.contMDiffAt (h : ContMDiff I I' n f) : 
ContMDiffAt I I' n f x
· 使用定理 `Bundle.contMDiff_proj`：contMDiff_proj : ContMDiff (IB.prod 𝓘(𝕜, F)) IB n
 (π F E)
-/
theorem contMDiffAt_proj {p : TotalSpace F E} : ContMDiffAt (IB.prod 𝓘(𝕜, F)) IB n (π F E) p :=
  (contMDiff_proj E).contMDiffAt
/-
**Bundle.contMDiffWithinAt_proj** 是 Mathlib 中的一个定理，位于命名空间 `Bundle`。
形式化陈述：contMDiffWithinAt_proj {s : Set (TotalSpace F E)} {p : TotalSpace F E} : C
ontMDiffWithinAt (IB.prod 𝓘(𝕜, F)) IB n (π F E) s p
参数：TotalSpace F E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffAt.contMDiffWithinAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {H : Type u_…
· 使用定理 `Bundle.contMDiffAt_proj`：contMDiffAt_proj {p : TotalSpace F E} : ContMDi
ffAt (IB.prod 𝓘(𝕜, F)) IB n (π F E) p
-/
theorem contMDiffWithinAt_proj {s : Set (TotalSpace F E)} {p : TotalSpace F E} :
    ContMDiffWithinAt (IB.prod 𝓘(𝕜, F)) IB n (π F E) s p :=
  (contMDiffAt_proj E).contMDiffWithinAt

section

variable (𝕜) [∀ x, AddCommMonoid (E x)]
variable [∀ x, Module 𝕜 (E x)] [VectorBundle 𝕜 F E]

/-
**Bundle.contMDiff_zeroSection** 是 Mathlib 中的一个定理，位于命名空间 `Bundle`。
形式化陈述：contMDiff_zeroSection : ContMDiff IB (IB.prod 𝓘(𝕜, F)) n (zeroSection F E)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.contMDiffAt_section`：contMDiffAt_section {s : forall x, E x} (x₀ 
: B) : ContMDiffAt IB (IB.prod 𝓘(𝕜, F)) n (fun x => TotalSpace.mk' F x (s x)) x₀
 ↔ ContMDiffAt I…
· 使用定理 `ContMDiffAt.congr_of_eventuallyEq`：ContMDiffAt.congr_of_eventuallyEq (h 
: ContMDiffAt I I' n f x) (h₁ : f₁ =ᶠ[𝓝 x] f) : ContMDiffAt I I' n f₁ x
· 使用定理 `contMDiffAt_const`：contMDiffAt_const : ContMDiffAt I I' n (fun _ : M => 
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
theorem contMDiff_zeroSection : ContMDiff IB (IB.prod 𝓘(𝕜, F)) n (zeroSection F E) := by
  intro x
  unfold zeroSection
  rw [contMDiffAt_section]
  apply (contMDiffAt_const (c := 0)).congr_of_eventuallyEq
  filter_upwards [(trivializationAt F E x).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt F E x)] with y hy
    using congr_arg Prod.snd <| (trivializationAt F E x).zeroSection 𝕜 hy
/-
**Bundle.contMDiffOn_zeroSection** 是 Mathlib 中的一个定理，位于命名空间 `Bundle`。
形式化陈述：contMDiffOn_zeroSection {t : Set B} : ContMDiffOn IB (IB.prod 𝓘(𝕜, F)) n (
zeroSection F E) t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiff.contMDiffOn`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
H : Type u_…
· 使用定理 `Bundle.contMDiff_zeroSection`：contMDiff_zeroSection : ContMDiff IB (IB.p
rod 𝓘(𝕜, F)) n (zeroSection F E)
-/
theorem contMDiffOn_zeroSection {t : Set B} :
    ContMDiffOn IB (IB.prod 𝓘(𝕜, F)) n (zeroSection F E) t :=
  (contMDiff_zeroSection _ _).contMDiffOn
/-
**Bundle.contMDiffAt_zeroSection** 是 Mathlib 中的一个定理，位于命名空间 `Bundle`。
形式化陈述：contMDiffAt_zeroSection {x : B} : ContMDiffAt IB (IB.prod 𝓘(𝕜, F)) n (zero
Section F E) x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiff.contMDiffAt`：ContMDiff.contMDiffAt (h : ContMDiff I I' n f) : 
ContMDiffAt I I' n f x
· 使用定理 `Bundle.contMDiff_zeroSection`：contMDiff_zeroSection : ContMDiff IB (IB.p
rod 𝓘(𝕜, F)) n (zeroSection F E)
-/
theorem contMDiffAt_zeroSection {x : B} : ContMDiffAt IB (IB.prod 𝓘(𝕜, F)) n (zeroSection F E) x :=
  (contMDiff_zeroSection _ _).contMDiffAt
/-
**Bundle.contMDiffWithinAt_zeroSection** 是 Mathlib 中的一个定理，位于命名空间 `Bundle`。
形式化陈述：contMDiffWithinAt_zeroSection {t : Set B} {x : B} : ContMDiffWithinAt IB (
IB.prod 𝓘(𝕜, F)) n (zeroSection F E) t x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffAt.contMDiffWithinAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {H : Type u_…
· 使用定理 `Bundle.contMDiff_zeroSection`：contMDiff_zeroSection : ContMDiff IB (IB.p
rod 𝓘(𝕜, F)) n (zeroSection F E)
-/
theorem contMDiffWithinAt_zeroSection {t : Set B} {x : B} :
    ContMDiffWithinAt IB (IB.prod 𝓘(𝕜, F)) n (zeroSection F E) t x :=
  (contMDiff_zeroSection _ _ x).contMDiffWithinAt

end

variable {s : ∀ x, E x} {u : Set B} {x : B}

@[nontriviality]
/-
**Bundle.contMDiffWithinAt_section_of_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 `Bu
ndle`。
形式化陈述：contMDiffWithinAt_section_of_subsingleton [Subsingleton F] : ContMDiffWith
inAt IB (IB.prod 𝓘(𝕜, F)) n (fun x => TotalSpace.mk' F x (s x)) u x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.contMDiffWithinAt_section`：contMDiffWithinAt_section {s : forall 
x, E x} {a : Set B} {x₀ : B} : ContMDiffWithinAt IB (IB.prod 𝓘(𝕜, F)) n (fun x =
> TotalSpace.mk' F x (…
· 使用定理 `ContMDiffWithinAt.congr`：ContMDiffWithinAt.congr (h : ContMDiffWithinAt 
I I' n f s x) (h₁ : forall y in s, f₁ y = f y) (hx : f₁ x = f x) : ContMDiffWith
inAt I I' n f…
· 使用定理 `contMDiffWithinAt_const`：contMDiffWithinAt_const : ContMDiffWithinAt I I
' n (fun _ : M => c) s x
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
lemma contMDiffWithinAt_section_of_subsingleton [Subsingleton F] :
    ContMDiffWithinAt IB (IB.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (s x)) u x := by
  rw [contMDiffWithinAt_section]
  apply contMDiffWithinAt_const |>.congr
  · intro y _
    apply Subsingleton.elim
  rfl

@[nontriviality]
/-
**Bundle.contMDiffAt_section_of_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 `Bundle`。
形式化陈述：contMDiffAt_section_of_subsingleton [Subsingleton F] : ContMDiffAt IB (IB.
prod 𝓘(𝕜, F)) n (fun x => TotalSpace.mk' F x (s x)) x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `contMDiffWithinAt_univ`：contMDiffWithinAt_univ : ContMDiffWithinAt I I' 
n f univ x ↔ ContMDiffAt I I' n f x
· 使用引理 `Bundle.contMDiffWithinAt_section_of_subsingleton`：contMDiffWithinAt_sect
ion_of_subsingleton [Subsingleton F] : ContMDiffWithinAt IB (IB.prod 𝓘(𝕜, F)) n 
(fun x => TotalSpace.mk' F x (s x)) u …
-/
lemma contMDiffAt_section_of_subsingleton [Subsingleton F] :
    ContMDiffAt IB (IB.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (s x)) x := by
  rw [← contMDiffWithinAt_univ]
  apply contMDiffWithinAt_section_of_subsingleton

@[nontriviality]
/-
**Bundle.contMDiffOn_section_of_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 `Bundle`。
形式化陈述：contMDiffOn_section_of_subsingleton [Subsingleton F] : ContMDiffOn IB (IB.
prod 𝓘(𝕜, F)) n (fun x => TotalSpace.mk' F x (s x)) u
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Bundle.contMDiffWithinAt_section_of_subsingleton`：contMDiffWithinAt_sect
ion_of_subsingleton [Subsingleton F] : ContMDiffWithinAt IB (IB.prod 𝓘(𝕜, F)) n 
(fun x => TotalSpace.mk' F x (s x)) u …
-/
lemma contMDiffOn_section_of_subsingleton [Subsingleton F] :
    ContMDiffOn IB (IB.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (s x)) u :=
  fun _x _hx ↦ contMDiffWithinAt_section_of_subsingleton ..

@[nontriviality]
/-
**Bundle.contMDiff_section_of_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 `Bundle`。
形式化陈述：contMDiff_section_of_subsingleton [Subsingleton F] : ContMDiff IB (IB.prod
 𝓘(𝕜, F)) n (fun x => TotalSpace.mk' F x (s x))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Bundle.contMDiffAt_section_of_subsingleton`：contMDiffAt_section_of_subsi
ngleton [Subsingleton F] : ContMDiffAt IB (IB.prod 𝓘(𝕜, F)) n (fun x => TotalSpa
ce.mk' F x (s x)) x
-/
lemma contMDiff_section_of_subsingleton [Subsingleton F] :
    ContMDiff IB (IB.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (s x)) :=
  fun _x ↦ contMDiffAt_section_of_subsingleton ..

end Bundle

end

/-! ### `C^n` vector bundles -/


variable [NontriviallyNormedField 𝕜] {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B]
  [ChartedSpace HB B] {EM : Type*} [NormedAddCommGroup EM]
  [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners 𝕜 EM HM}
  [TopologicalSpace M] [ChartedSpace HM M]
  [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

section WithTopology

variable [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)] (F E)
variable [FiberBundle F E] [VectorBundle 𝕜 F E]

variable (n IB) in
/-- When `B` is a manifold with respect to a model `IB` and `E` is a
topological vector bundle over `B` with fibers isomorphic to `F`,
then `ContMDiffVectorBundle n F E IB` registers that the bundle is `C^n`, in the sense of having
`C^n` transition functions. This is a mixin, not carrying any new data. -/
/-
**ContMDiffVectorBundle** 是 Mathlib 中的一个类，位于命名空间 ``。
形式化陈述：ContMDiffVectorBundle : Prop where protected contMDiffOn_coordChangeL : fo
rall (e e' : Trivialization F (π F E)) [MemTrivializationAtlas e] [MemTrivializa
tionAtlas e'], ContMDiffOn IB 𝓘(𝕜, F ->L[𝕜] F) n (fun b : B => (e.coordChangeL 𝕜
 e' b : F ->L[𝕜] F)) (e.baseSet inter e'.baseSet)  variable {F E} in protected t
heorem ContMDiffVectorBundle.of_le {m n : Nat∞ω} (hmn : m <= n) [h : ContMDiffVe
ctorBundle n F E IB] : ContMDiffVectorBundle m F E IB
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `B` is a manifold with respect to a model `IB` and `E` is a
topological vector bundle over `B` with fibers isomorphic to `F`,
then `ContMDiffVectorBundle n F E IB` registers that the bundle is `C^n`, in the
 sense of having
`C^n` transition functions. This is a mixin, not carrying any new data.
-/
class ContMDiffVectorBundle : Prop where
  protected contMDiffOn_coordChangeL :
    ∀ (e e' : Trivialization F (π F E)) [MemTrivializationAtlas e] [MemTrivializationAtlas e'],
      ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] F) n (fun b : B => (e.coordChangeL 𝕜 e' b : F →L[𝕜] F))
        (e.baseSet ∩ e'.baseSet)

variable {F E} in
/-
**ContMDiffVectorBundle.of_le** 是 Mathlib 中的一个定理，位于命名空间 `ContMDiffVectorBundle`。
形式化陈述：∀ {𝕜 : Type u_1} {B : Type u_2} {F : Type u_4} {E : B → Type u_6} [inst : 
NontriviallyNormedField 𝕜] {EB : Type u_7}   [inst_1 : NormedAddCommGroup EB] [i
nst_2 : NormedSpace 𝕜 EB] {HB : Type u_8} [inst_3 : TopologicalSpace HB]   {IB :
 ModelWithCorners 𝕜 EB HB} [inst_4 : TopologicalSpace B] [inst_5 : ChartedSpace 
HB B]   [inst_6 : (x : B) → AddCommMonoid (E x)] [inst_7 : (x : B) → _root_.Modu
le 𝕜 (E x)] [inst_8 : NormedAddCommGroup F]   [inst_9 : NormedSpace 𝕜 F] [inst_1
0 : TopologicalSpace (Bundle.TotalSpace F E)]   [inst_11 : (x : B) → Topological
Space (E x)] [inst_12 : FiberBundle F E] [inst_13 : VectorBundle 𝕜 F E]   {m n :
 WithTop ℕ∞}, m ≤ n → ∀ [h : ContMDiffVectorBundle n F E IB], ContMDiffVectorBun
dle m F E IB
参数：x : B；E x；x : B；E x；Bundle.TotalSpace F E；x : B；E x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffOn.of_le`：ContMDiffOn.of_le (hf : ContMDiffOn I I' n f s) (le :
 m <= n) : ContMDiffOn I I' m f s
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `trivialization_linear`：∀ (R : Type u_1) {B : Type u_2} {F : Type u_3} {E
 : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x : B) → AddCom
mMonoid (E …
· 使用定理 `ContMDiffVectorBundle.contMDiffOn_coordChangeL`：∀ {n : WithTop ℕ∞} {𝕜 : 
Type u_1} {B : Type u_2} {F : Type u_4} {E : B → Type u_6} {inst : NontriviallyN
ormedField 𝕜}   {EB : Type u_7} {ins…
-/
protected theorem ContMDiffVectorBundle.of_le {m n : ℕ∞ω} (hmn : m ≤ n)
    [h : ContMDiffVectorBundle n F E IB] : ContMDiffVectorBundle m F E IB :=
  ⟨fun e e' _ _ ↦ (h.contMDiffOn_coordChangeL e e').of_le hmn⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {a : ℕ∞ω} [ContMDiffVectorBundle ∞ F E IB] [h : ENat.LEInfty a] :
    ContMDiffVectorBundle a F E IB :=
  ContMDiffVectorBundle.of_le h.out
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {a : ℕ∞ω} [ContMDiffVectorBundle ω F E IB] : ContMDiffVectorBundle a F E IB :=
  ContMDiffVectorBundle.of_le le_top
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [ContMDiffVectorBundle 2 F E IB] : ContMDiffVectorBundle 1 F E IB :=
  ContMDiffVectorBundle.of_le one_le_two
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ContMDiffVectorBundle 0 F E IB := by
  constructor
  intro e e' he he'
  rw [contMDiffOn_zero_iff]
  exact VectorBundle.continuousOn_coordChange' e e'

variable [ContMDiffVectorBundle n F E IB]

section ContMDiffCoordChange

variable {F E}
variable (e e' : Trivialization F (π F E)) [MemTrivializationAtlas e] [MemTrivializationAtlas e']

/-
**contMDiffOn_coordChangeL** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffOn_coordChangeL : ContMDiffOn IB 𝓘(𝕜, F ->L[𝕜] F) n (fun b : B =>
 (e.coordChangeL 𝕜 e' b : F ->L[𝕜] F)) (e.baseSet inter e'.baseSet)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffVectorBundle.contMDiffOn_coordChangeL`：∀ {n : WithTop ℕ∞} {𝕜 : 
Type u_1} {B : Type u_2} {F : Type u_4} {E : B → Type u_6} {inst : NontriviallyN
ormedField 𝕜}   {EB : Type u_7} {ins…
-/
theorem contMDiffOn_coordChangeL :
    ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] F) n (fun b : B => (e.coordChangeL 𝕜 e' b : F →L[𝕜] F))
      (e.baseSet ∩ e'.baseSet) :=
  ContMDiffVectorBundle.contMDiffOn_coordChangeL e e'
/-
**contMDiffOn_symm_coordChangeL** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffOn_symm_coordChangeL : ContMDiffOn IB 𝓘(𝕜, F ->L[𝕜] F) n (fun b :
 B => ((e.coordChangeL 𝕜 e' b).symm : F ->L[𝕜] F)) (e.baseSet inter e'.baseSet)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `trivialization_linear`：∀ (R : Type u_1) {B : Type u_2} {F : Type u_3} {E
 : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x : B) → AddCom
mMonoid (E …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `ContMDiffOn.congr`：ContMDiffOn.congr (h : ContMDiffOn I I' n f s) (h₁ : 
forall y in s, f₁ y = f y) : ContMDiffOn I I' n f₁ s
· 使用定理 `ContMDiffVectorBundle.contMDiffOn_coordChangeL`：∀ {n : WithTop ℕ∞} {𝕜 : 
Type u_1} {B : Type u_2} {F : Type u_4} {E : B → Type u_6} {inst : NontriviallyN
ormedField 𝕜}   {EB : Type u_7} {ins…
· 使用定理 `Bundle.Trivialization.symm_coordChangeL`：∀ {R : Type u_1} {B : Type u_2}
 {F : Type u_3} {E : B → Type u_4} [inst : Semiring R] [inst_1 : TopologicalSpac
e F]   [inst_2 : TopologicalS…
-/
theorem contMDiffOn_symm_coordChangeL :
    ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] F) n (fun b : B => ((e.coordChangeL 𝕜 e' b).symm : F →L[𝕜] F))
      (e.baseSet ∩ e'.baseSet) := by
  rw [inter_comm]
  refine (ContMDiffVectorBundle.contMDiffOn_coordChangeL e' e).congr fun b hb ↦ ?_
  rw [e.symm_coordChangeL e' hb]

variable {e e'}
/-
**contMDiffAt_coordChangeL** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffAt_coordChangeL {x : B} (h : x in e.baseSet) (h' : x in e'.baseSe
t) : ContMDiffAt IB 𝓘(𝕜, F ->L[𝕜] F) n (fun b : B => (e.coordChangeL 𝕜 e' b : F 
->L[𝕜] F)) x
参数：h : x in e.baseSet；h' : x in e'.baseSet。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffOn.contMDiffAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFiel
d 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E]
 {H : Type u_…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `trivialization_linear`：∀ (R : Type u_1) {B : Type u_2} {F : Type u_3} {E
 : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x : B) → AddCom
mMonoid (E …
· 使用定理 `contMDiffOn_coordChangeL`：contMDiffOn_coordChangeL : ContMDiffOn IB 𝓘(𝕜,
 F ->L[𝕜] F) n (fun b : B => (e.coordChangeL 𝕜 e' b : F ->L[𝕜] F)) (e.baseSet in
ter e'.baseSet…
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
· 使用定理 `Bundle.Trivialization.open_baseSet`：∀ {B : Type u_1} {F : Type u_2} {Z :
 Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 :
 TopologicalSpace Z] {pr…
-/
theorem contMDiffAt_coordChangeL {x : B} (h : x ∈ e.baseSet) (h' : x ∈ e'.baseSet) :
    ContMDiffAt IB 𝓘(𝕜, F →L[𝕜] F) n (fun b : B => (e.coordChangeL 𝕜 e' b : F →L[𝕜] F)) x :=
  (contMDiffOn_coordChangeL e e').contMDiffAt <|
    (e.open_baseSet.inter e'.open_baseSet).mem_nhds ⟨h, h'⟩

variable {s : Set M} {f : M → B} {g : M → F} {x : M}
/-
**ContMDiffWithinAt.coordChangeL** 是 Mathlib 中的一个定理，位于命名空间 `ContMDiffWithinAt`。
形式化陈述：∀ {n : WithTop ℕ∞} {𝕜 : Type u_1} {B : Type u_2} {F : Type u_4} {M : Type 
u_5} {E : B → Type u_6}   [inst : NontriviallyNormedField 𝕜] {EB : Type u_7} [in
st_1 : NormedAddCommGroup EB] [inst_2 : NormedSpace 𝕜 EB]   {HB : Type u_8} [ins
t_3 : TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB} [inst_4 : Topological
Space B]   [inst_5 : ChartedSpace HB B] {EM : Type u_9} [inst_6 : NormedAddCommG
roup EM] [inst_7 : NormedSpace 𝕜 EM]   {HM : Type u_10} [inst_8 : TopologicalSpa
ce HM] {IM : ModelWithCorners 𝕜 EM HM} [inst_9 : TopologicalSpace M]   [inst_10 
: ChartedSpace HM M] [inst_11 : (x : B) → AddCommMonoid (E x)] [inst_12 : (x : B
) → _root_.Module 𝕜 (E x)]   [inst_13 : NormedAddCommGroup F] [inst_14 : NormedS
pace 𝕜 F] [inst_15 : TopologicalSpace (Bundle.TotalSpace F E)]   [inst_16 : (x :
 B) → TopologicalSpace (E x)] [inst_17 : FiberBundle F E] [inst_18 : VectorBundl
e 𝕜 F E]   [ContMDiffVectorBundle n F E IB] {e e' : Bundle.Trivialization F Bund
le.TotalSpace.proj}   [inst_20 : MemTrivializationAtlas e] [inst_21 : MemTrivial
izationAtlas e'] {s : Set M} {f : M → B} {x : M},   ContMDiffWithinAt IM IB n f 
s x →     f x ∈ e.baseSet →       f x ∈ e'.baseSet →         ContMDiffWithinAt I
M (modelWithCornersSelf 𝕜 (F →L[𝕜] F)) n           (fun y => ↑(Bundle.Trivializa
tion.coordChangeL 𝕜 e e' (f y))) s x
参数：x : B；E x；x : B；E x；Bundle.TotalSpace F E；x : B；E x；modelWithCornersSelf 𝕜 (F
 →L[𝕜] F)；fun y => ↑(Bundle.Trivialization.coordChangeL 𝕜 e e' (f y))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffAt.comp_contMDiffWithinAt`：ContMDiffAt.comp_contMDiffWithinAt {
g : M' -> M''} (x : M) (hg : ContMDiffAt I' I'' n g (f x)) (hf : ContMDiffWithin
At I I' n f s x) : ContM…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `trivialization_linear`：∀ (R : Type u_1) {B : Type u_2} {F : Type u_3} {E
 : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x : B) → AddCom
mMonoid (E …
· 使用定理 `contMDiffAt_coordChangeL`：contMDiffAt_coordChangeL {x : B} (h : x in e.b
aseSet) (h' : x in e'.baseSet) : ContMDiffAt IB 𝓘(𝕜, F ->L[𝕜] F) n (fun b : B =>
 (e.coordChang…
-/
protected theorem ContMDiffWithinAt.coordChangeL
    (hf : ContMDiffWithinAt IM IB n f s x) (he : f x ∈ e.baseSet) (he' : f x ∈ e'.baseSet) :
    ContMDiffWithinAt IM 𝓘(𝕜, F →L[𝕜] F) n (fun y ↦ (e.coordChangeL 𝕜 e' (f y) : F →L[𝕜] F)) s x :=
  (contMDiffAt_coordChangeL he he').comp_contMDiffWithinAt _ hf

protected nonrec theorem ContMDiffAt.coordChangeL
    (hf : ContMDiffAt IM IB n f x) (he : f x ∈ e.baseSet) (he' : f x ∈ e'.baseSet) :
    ContMDiffAt IM 𝓘(𝕜, F →L[𝕜] F) n (fun y ↦ (e.coordChangeL 𝕜 e' (f y) : F →L[𝕜] F)) x :=
  hf.coordChangeL he he'
/-
**ContMDiffOn.coordChangeL** 是 Mathlib 中的一个定理，位于命名空间 `ContMDiffOn`。
形式化陈述：∀ {n : WithTop ℕ∞} {𝕜 : Type u_1} {B : Type u_2} {F : Type u_4} {M : Type 
u_5} {E : B → Type u_6}   [inst : NontriviallyNormedField 𝕜] {EB : Type u_7} [in
st_1 : NormedAddCommGroup EB] [inst_2 : NormedSpace 𝕜 EB]   {HB : Type u_8} [ins
t_3 : TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB} [inst_4 : Topological
Space B]   [inst_5 : ChartedSpace HB B] {EM : Type u_9} [inst_6 : NormedAddCommG
roup EM] [inst_7 : NormedSpace 𝕜 EM]   {HM : Type u_10} [inst_8 : TopologicalSpa
ce HM] {IM : ModelWithCorners 𝕜 EM HM} [inst_9 : TopologicalSpace M]   [inst_10 
: ChartedSpace HM M] [inst_11 : (x : B) → AddCommMonoid (E x)] [inst_12 : (x : B
) → _root_.Module 𝕜 (E x)]   [inst_13 : NormedAddCommGroup F] [inst_14 : NormedS
pace 𝕜 F] [inst_15 : TopologicalSpace (Bundle.TotalSpace F E)]   [inst_16 : (x :
 B) → TopologicalSpace (E x)] [inst_17 : FiberBundle F E] [inst_18 : VectorBundl
e 𝕜 F E]   [ContMDiffVectorBundle n F E IB] {e e' : Bundle.Trivialization F Bund
le.TotalSpace.proj}   [inst_20 : MemTrivializationAtlas e] [inst_21 : MemTrivial
izationAtlas e'] {s : Set M} {f : M → B},   ContMDiffOn IM IB n f s →     Set.Ma
psTo f s e.baseSet →       Set.MapsTo f s e'.baseSet →         ContMDiffOn IM (m
odelWithCornersSelf 𝕜 (F →L[𝕜] F)) n           (fun y => ↑(Bundle.Trivialization
.coordChangeL 𝕜 e e' (f y))) s
参数：x : B；E x；x : B；E x；Bundle.TotalSpace F E；x : B；E x；modelWithCornersSelf 𝕜 (F
 →L[𝕜] F)；fun y => ↑(Bundle.Trivialization.coordChangeL 𝕜 e e' (f y))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffWithinAt.coordChangeL`：∀ {n : WithTop ℕ∞} {𝕜 : Type u_1} {B : T
ype u_2} {F : Type u_4} {M : Type u_5} {E : B → Type u_6}   [inst : Nontrivially
NormedField 𝕜] {EB :…
-/
protected theorem ContMDiffOn.coordChangeL
    (hf : ContMDiffOn IM IB n f s) (he : MapsTo f s e.baseSet) (he' : MapsTo f s e'.baseSet) :
    ContMDiffOn IM 𝓘(𝕜, F →L[𝕜] F) n (fun y ↦ (e.coordChangeL 𝕜 e' (f y) : F →L[𝕜] F)) s :=
  fun x hx ↦ (hf x hx).coordChangeL (he hx) (he' hx)
/-
**ContMDiff.coordChangeL** 是 Mathlib 中的一个定理，位于命名空间 `ContMDiff`。
形式化陈述：∀ {n : WithTop ℕ∞} {𝕜 : Type u_1} {B : Type u_2} {F : Type u_4} {M : Type 
u_5} {E : B → Type u_6}   [inst : NontriviallyNormedField 𝕜] {EB : Type u_7} [in
st_1 : NormedAddCommGroup EB] [inst_2 : NormedSpace 𝕜 EB]   {HB : Type u_8} [ins
t_3 : TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB} [inst_4 : Topological
Space B]   [inst_5 : ChartedSpace HB B] {EM : Type u_9} [inst_6 : NormedAddCommG
roup EM] [inst_7 : NormedSpace 𝕜 EM]   {HM : Type u_10} [inst_8 : TopologicalSpa
ce HM] {IM : ModelWithCorners 𝕜 EM HM} [inst_9 : TopologicalSpace M]   [inst_10 
: ChartedSpace HM M] [inst_11 : (x : B) → AddCommMonoid (E x)] [inst_12 : (x : B
) → _root_.Module 𝕜 (E x)]   [inst_13 : NormedAddCommGroup F] [inst_14 : NormedS
pace 𝕜 F] [inst_15 : TopologicalSpace (Bundle.TotalSpace F E)]   [inst_16 : (x :
 B) → TopologicalSpace (E x)] [inst_17 : FiberBundle F E] [inst_18 : VectorBundl
e 𝕜 F E]   [ContMDiffVectorBundle n F E IB] {e e' : Bundle.Trivialization F Bund
le.TotalSpace.proj}   [inst_20 : MemTrivializationAtlas e] [inst_21 : MemTrivial
izationAtlas e'] {f : M → B},   ContMDiff IM IB n f →     (∀ (x : M), f x ∈ e.ba
seSet) →       (∀ (x : M), f x ∈ e'.baseSet) →         ContMDiff IM (modelWithCo
rnersSelf 𝕜 (F →L[𝕜] F)) n fun y => ↑(Bundle.Trivialization.coordChangeL 𝕜 e e' 
(f y))
参数：x : B；E x；x : B；E x；Bundle.TotalSpace F E；x : B；E x；∀ (x : M), f x ∈ e.baseSe
t；∀ (x : M), f x ∈ e'.baseSet；modelWithCornersSelf 𝕜 (F →L[𝕜] F)；Bundle.Triviali
zation.coordChangeL 𝕜 e e' (f y)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffAt.coordChangeL`：∀ {n : WithTop ℕ∞} {𝕜 : Type u_1} {B : Type u_
2} {F : Type u_4} {M : Type u_5} {E : B → Type u_6}   [inst : NontriviallyNormed
Field 𝕜] {EB :…
-/
protected theorem ContMDiff.coordChangeL
    (hf : ContMDiff IM IB n f) (he : ∀ x, f x ∈ e.baseSet) (he' : ∀ x, f x ∈ e'.baseSet) :
    ContMDiff IM 𝓘(𝕜, F →L[𝕜] F) n (fun y ↦ (e.coordChangeL 𝕜 e' (f y) : F →L[𝕜] F)) := fun x ↦
  (hf x).coordChangeL (he x) (he' x)
/-
**ContMDiffWithinAt.coordChange** 是 Mathlib 中的一个定理，位于命名空间 `ContMDiffWithinAt`。
形式化陈述：∀ {n : WithTop ℕ∞} {𝕜 : Type u_1} {B : Type u_2} {F : Type u_4} {M : Type 
u_5} {E : B → Type u_6}   [inst : NontriviallyNormedField 𝕜] {EB : Type u_7} [in
st_1 : NormedAddCommGroup EB] [inst_2 : NormedSpace 𝕜 EB]   {HB : Type u_8} [ins
t_3 : TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB} [inst_4 : Topological
Space B]   [inst_5 : ChartedSpace HB B] {EM : Type u_9} [inst_6 : NormedAddCommG
roup EM] [inst_7 : NormedSpace 𝕜 EM]   {HM : Type u_10} [inst_8 : TopologicalSpa
ce HM] {IM : ModelWithCorners 𝕜 EM HM} [inst_9 : TopologicalSpace M]   [inst_10 
: ChartedSpace HM M] [inst_11 : (x : B) → AddCommMonoid (E x)] [inst_12 : (x : B
) → _root_.Module 𝕜 (E x)]   [inst_13 : NormedAddCommGroup F] [inst_14 : NormedS
pace 𝕜 F] [inst_15 : TopologicalSpace (Bundle.TotalSpace F E)]   [inst_16 : (x :
 B) → TopologicalSpace (E x)] [inst_17 : FiberBundle F E] [inst_18 : VectorBundl
e 𝕜 F E]   [ContMDiffVectorBundle n F E IB] {e e' : Bundle.Trivialization F Bund
le.TotalSpace.proj} [MemTrivializationAtlas e]   [MemTrivializationAtlas e'] {s 
: Set M} {f : M → B} {g : M → F} {x : M},   ContMDiffWithinAt IM IB n f s x →   
  ContMDiffWithinAt IM (modelWithCornersSelf 𝕜 F) n g s x →       f x ∈ e.baseSe
t →         f x ∈ e'.baseSet → ContMDiffWithinAt IM (modelWithCornersSelf 𝕜 F) n
 (fun y => e.coordChange e' (f y) (g y)) s x
参数：x : B；E x；x : B；E x；Bundle.TotalSpace F E；x : B；E x；modelWithCornersSelf 𝕜 F；
modelWithCornersSelf 𝕜 F；fun y => e.coordChange e' (f y) (g y)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffWithinAt.congr_of_eventuallyEq`：ContMDiffWithinAt.congr_of_even
tuallyEq (h : ContMDiffWithinAt I I' n f s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x 
= f x) : ContMDiffWithinAt I …
· 使用定理 `trivialization_linear`：∀ (R : Type u_1) {B : Type u_2} {F : Type u_3} {E
 : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x : B) → AddCom
mMonoid (E …
· 使用定理 `ContMDiffWithinAt.clm_apply`：ContMDiffWithinAt.clm_apply {g : M -> F₁ ->
L[𝕜] F₂} {f : M -> F₁} {s : Set M} {x : M} (hg : ContMDiffWithinAt I 𝓘(𝕜, F₁ ->L
[𝕜] F₂) n g s x) …
· 使用定理 `ContMDiffWithinAt.coordChangeL`：∀ {n : WithTop ℕ∞} {𝕜 : Type u_1} {B : T
ype u_2} {F : Type u_4} {M : Type u_5} {E : B → Type u_6}   [inst : Nontrivially
NormedField 𝕜] {EB :…
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
· 使用定理 `Bundle.Trivialization.open_baseSet`：∀ {B : Type u_1} {F : Type u_2} {Z :
 Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 :
 TopologicalSpace Z] {pr…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `ContMDiffWithinAt.continuousWithinAt`：ContMDiffWithinAt.continuousWithin
At (hf : ContMDiffWithinAt I I' n f s x) : ContinuousWithinAt f s x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Bundle.Trivialization.coordChangeL_apply'`：∀ {R : Type u_1} {B : Type u_
2} {F : Type u_3} {E : B → Type u_4} [inst : Semiring R] [inst_1 : TopologicalSp
ace F]   [inst_2 : TopologicalS…
-/
protected theorem ContMDiffWithinAt.coordChange
    (hf : ContMDiffWithinAt IM IB n f s x) (hg : ContMDiffWithinAt IM 𝓘(𝕜, F) n g s x)
    (he : f x ∈ e.baseSet) (he' : f x ∈ e'.baseSet) :
    ContMDiffWithinAt IM 𝓘(𝕜, F) n (fun y ↦ e.coordChange e' (f y) (g y)) s x := by
  refine ((hf.coordChangeL he he').clm_apply hg).congr_of_eventuallyEq ?_ ?_
  · have : e.baseSet ∩ e'.baseSet ∈ 𝓝 (f x) :=
     (e.open_baseSet.inter e'.open_baseSet).mem_nhds ⟨he, he'⟩
    filter_upwards [hf.continuousWithinAt this] with y hy
    exact (Trivialization.coordChangeL_apply' e e' hy (g y)).symm
  · exact (Trivialization.coordChangeL_apply' e e' ⟨he, he'⟩ (g x)).symm

protected nonrec theorem ContMDiffAt.coordChange
    (hf : ContMDiffAt IM IB n f x) (hg : ContMDiffAt IM 𝓘(𝕜, F) n g x) (he : f x ∈ e.baseSet)
    (he' : f x ∈ e'.baseSet) :
    ContMDiffAt IM 𝓘(𝕜, F) n (fun y ↦ e.coordChange e' (f y) (g y)) x :=
  hf.coordChange hg he he'
/-
**ContMDiffOn.coordChange** 是 Mathlib 中的一个定理，位于命名空间 `ContMDiffOn`。
形式化陈述：∀ {n : WithTop ℕ∞} {𝕜 : Type u_1} {B : Type u_2} {F : Type u_4} {M : Type 
u_5} {E : B → Type u_6}   [inst : NontriviallyNormedField 𝕜] {EB : Type u_7} [in
st_1 : NormedAddCommGroup EB] [inst_2 : NormedSpace 𝕜 EB]   {HB : Type u_8} [ins
t_3 : TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB} [inst_4 : Topological
Space B]   [inst_5 : ChartedSpace HB B] {EM : Type u_9} [inst_6 : NormedAddCommG
roup EM] [inst_7 : NormedSpace 𝕜 EM]   {HM : Type u_10} [inst_8 : TopologicalSpa
ce HM] {IM : ModelWithCorners 𝕜 EM HM} [inst_9 : TopologicalSpace M]   [inst_10 
: ChartedSpace HM M] [inst_11 : (x : B) → AddCommMonoid (E x)] [inst_12 : (x : B
) → _root_.Module 𝕜 (E x)]   [inst_13 : NormedAddCommGroup F] [inst_14 : NormedS
pace 𝕜 F] [inst_15 : TopologicalSpace (Bundle.TotalSpace F E)]   [inst_16 : (x :
 B) → TopologicalSpace (E x)] [inst_17 : FiberBundle F E] [inst_18 : VectorBundl
e 𝕜 F E]   [ContMDiffVectorBundle n F E IB] {e e' : Bundle.Trivialization F Bund
le.TotalSpace.proj} [MemTrivializationAtlas e]   [MemTrivializationAtlas e'] {s 
: Set M} {f : M → B} {g : M → F},   ContMDiffOn IM IB n f s →     ContMDiffOn IM
 (modelWithCornersSelf 𝕜 F) n g s →       Set.MapsTo f s e.baseSet →         Set
.MapsTo f s e'.baseSet →           ContMDiffOn IM (modelWithCornersSelf 𝕜 F) n (
fun y => e.coordChange e' (f y) (g y)) s
参数：x : B；E x；x : B；E x；Bundle.TotalSpace F E；x : B；E x；modelWithCornersSelf 𝕜 F；
modelWithCornersSelf 𝕜 F；fun y => e.coordChange e' (f y) (g y)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffWithinAt.coordChange`：∀ {n : WithTop ℕ∞} {𝕜 : Type u_1} {B : Ty
pe u_2} {F : Type u_4} {M : Type u_5} {E : B → Type u_6}   [inst : NontriviallyN
ormedField 𝕜] {EB :…
-/
protected theorem ContMDiffOn.coordChange (hf : ContMDiffOn IM IB n f s)
    (hg : ContMDiffOn IM 𝓘(𝕜, F) n g s) (he : MapsTo f s e.baseSet) (he' : MapsTo f s e'.baseSet) :
    ContMDiffOn IM 𝓘(𝕜, F) n (fun y ↦ e.coordChange e' (f y) (g y)) s := fun x hx ↦
  (hf x hx).coordChange (hg x hx) (he hx) (he' hx)
/-
**ContMDiff.coordChange** 是 Mathlib 中的一个定理，位于命名空间 `ContMDiff`。
形式化陈述：∀ {n : WithTop ℕ∞} {𝕜 : Type u_1} {B : Type u_2} {F : Type u_4} {M : Type 
u_5} {E : B → Type u_6}   [inst : NontriviallyNormedField 𝕜] {EB : Type u_7} [in
st_1 : NormedAddCommGroup EB] [inst_2 : NormedSpace 𝕜 EB]   {HB : Type u_8} [ins
t_3 : TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB} [inst_4 : Topological
Space B]   [inst_5 : ChartedSpace HB B] {EM : Type u_9} [inst_6 : NormedAddCommG
roup EM] [inst_7 : NormedSpace 𝕜 EM]   {HM : Type u_10} [inst_8 : TopologicalSpa
ce HM] {IM : ModelWithCorners 𝕜 EM HM} [inst_9 : TopologicalSpace M]   [inst_10 
: ChartedSpace HM M] [inst_11 : (x : B) → AddCommMonoid (E x)] [inst_12 : (x : B
) → _root_.Module 𝕜 (E x)]   [inst_13 : NormedAddCommGroup F] [inst_14 : NormedS
pace 𝕜 F] [inst_15 : TopologicalSpace (Bundle.TotalSpace F E)]   [inst_16 : (x :
 B) → TopologicalSpace (E x)] [inst_17 : FiberBundle F E] [inst_18 : VectorBundl
e 𝕜 F E]   [ContMDiffVectorBundle n F E IB] {e e' : Bundle.Trivialization F Bund
le.TotalSpace.proj} [MemTrivializationAtlas e]   [MemTrivializationAtlas e'] {f 
: M → B} {g : M → F},   ContMDiff IM IB n f →     ContMDiff IM (modelWithCorners
Self 𝕜 F) n g →       (∀ (x : M), f x ∈ e.baseSet) →         (∀ (x : M), f x ∈ e
'.baseSet) → ContMDiff IM (modelWithCornersSelf 𝕜 F) n fun y => e.coordChange e'
 (f y) (g y)
参数：x : B；E x；x : B；E x；Bundle.TotalSpace F E；x : B；E x；modelWithCornersSelf 𝕜 F；
∀ (x : M), f x ∈ e.baseSet；∀ (x : M), f x ∈ e'.baseSet；modelWithCornersSelf 𝕜 F；
f y；g y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffAt.coordChange`：∀ {n : WithTop ℕ∞} {𝕜 : Type u_1} {B : Type u_2
} {F : Type u_4} {M : Type u_5} {E : B → Type u_6}   [inst : NontriviallyNormedF
ield 𝕜] {EB :…
-/
protected theorem ContMDiff.coordChange (hf : ContMDiff IM IB n f)
    (hg : ContMDiff IM 𝓘(𝕜, F) n g) (he : ∀ x, f x ∈ e.baseSet) (he' : ∀ x, f x ∈ e'.baseSet) :
    ContMDiff IM 𝓘(𝕜, F) n (fun y ↦ e.coordChange e' (f y) (g y)) := fun x ↦
  (hf x).coordChange (hg x) (he x) (he' x)

variable (e e')

variable (IB) in
/-
**Bundle.Trivialization.contMDiffOn_symm_trans** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Bundle.Trivialization.contMDiffOn_symm_trans : ContMDiffOn (IB.prod 𝓘(𝕜, F
)) (IB.prod 𝓘(𝕜, F)) n (e.toOpenPartialHomeomorph.symm ≫ₕ e'.toOpenPartialHomeom
orph) (e.target inter e'.target)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Bundle.Trivialization.mem_target`：∀ {B : Type u_1} {F : Type u_2} {Z : T
ype u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z → B
}   [inst_2 : Topologi…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ContMDiffOn.congr`：ContMDiffOn.congr (h : ContMDiffOn I I' n f s) (h₁ : 
forall y in s, f₁ y = f y) : ContMDiffOn I I' n f₁ s
· 使用定理 `ContMDiffOn.prodMk`：ContMDiffOn.prodMk {f : M -> M'} {g : M -> N'} (hf :
 ContMDiffOn I I' n f s) (hg : ContMDiffOn I J' n g s) : ContMDiffOn I (I'.prod 
J') n (f…
· 使用定理 `contMDiffOn_fst`：contMDiffOn_fst {s : Set (M × N)} : ContMDiffOn (I.prod
 J) I n Prod.fst s
· 使用定理 `ContMDiffOn.coordChange`：∀ {n : WithTop ℕ∞} {𝕜 : Type u_1} {B : Type u_2
} {F : Type u_4} {M : Type u_5} {E : B → Type u_6}   [inst : NontriviallyNormedF
ield 𝕜] {EB :…
· 使用定理 `contMDiffOn_snd`：contMDiffOn_snd {s : Set (M × N)} : ContMDiffOn (I.prod
 J) J n Prod.snd s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mapsTo_inter`：mapsTo_inter : MapsTo f s (t₁ inter t₂) ↔ MapsTo f s t
₁ ∧ MapsTo f s t₂
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Bundle.Trivialization.symm_coe_proj`：∀ {B : Type u_1} {F : Type u_2} {E 
: B → Type u_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [ins
t_2 : TopologicalSpace (B…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Bundle.Trivialization.coe_fst'`：∀ {B : Type u_1} {F : Type u_2} {Z : Typ
e u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z → B} 
  [inst_2 : Topologi…
· 使用定理 `Bundle.Trivialization.proj_symm_apply`：∀ {B : Type u_1} {F : Type u_2} {
Z : Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : 
Z → B}   [inst_2 : Topologi…
-/
theorem Bundle.Trivialization.contMDiffOn_symm_trans :
    ContMDiffOn (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) n
      (e.toOpenPartialHomeomorph.symm ≫ₕ e'.toOpenPartialHomeomorph) (e.target ∩ e'.target) := by
  have Hmaps : MapsTo Prod.fst (e.target ∩ e'.target) (e.baseSet ∩ e'.baseSet) := fun x hx ↦
    ⟨e.mem_target.1 hx.1, e'.mem_target.1 hx.2⟩
  rw [mapsTo_inter] at Hmaps
  -- TODO: drop `congr` https://github.com/leanprover-community/mathlib4/issues/5473
  refine (contMDiffOn_fst.prodMk
    (contMDiffOn_fst.coordChange contMDiffOn_snd Hmaps.1 Hmaps.2)).congr ?_
  rintro ⟨b, x⟩ hb
  refine Prod.ext ?_ rfl
  have : (e.toOpenPartialHomeomorph.symm (b, x)).1 ∈ e'.baseSet := by
    simp_all only [Trivialization.mem_target, mfld_simps]
  exact (e'.coe_fst' this).trans (e.proj_symm_apply hb.1)

variable {e e'}
/-
**ContMDiffWithinAt.change_section_trivialization** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffWithinAt.change_section_trivialization {f : M -> TotalSpace F E} 
(hp : ContMDiffWithinAt IM IB n (π F E ∘ f) s x) (hf : ContMDiffWithinAt IM 𝓘(𝕜,
 F) n (fun y => (e (f y)).2) s x) (he : f x in e.source) (he' : f x in e'.source
) : ContMDiffWithinAt IM 𝓘(𝕜, F) n (fun y => (e' (f y)).2) s x
参数：hp : ContMDiffWithinAt IM IB n (π F E ∘ f) s x；hf : ContMDiffWithinAt IM 𝓘(𝕜,
 F) n (fun y => (e (f y)).2) s x；he : f x in e.source；he' : f x in e'.source。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffWithinAt.congr_of_eventuallyEq`：ContMDiffWithinAt.congr_of_even
tuallyEq (h : ContMDiffWithinAt I I' n f s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x 
= f x) : ContMDiffWithinAt I …
· 使用定理 `ContMDiffWithinAt.coordChange`：∀ {n : WithTop ℕ∞} {𝕜 : Type u_1} {B : Ty
pe u_2} {F : Type u_4} {M : Type u_5} {E : B → Type u_6}   [inst : NontriviallyN
ormedField 𝕜] {EB :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.Trivialization.mem_source`：∀ {B : Type u_1} {F : Type u_2} {Z : T
ype u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z → B
}   [inst_2 : Topologi…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `ContMDiffWithinAt.continuousWithinAt`：ContMDiffWithinAt.continuousWithin
At (hf : ContMDiffWithinAt I I' n f s x) : ContinuousWithinAt f s x
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
theorem ContMDiffWithinAt.change_section_trivialization {f : M → TotalSpace F E}
    (hp : ContMDiffWithinAt IM IB n (π F E ∘ f) s x)
    (hf : ContMDiffWithinAt IM 𝓘(𝕜, F) n (fun y ↦ (e (f y)).2) s x)
    (he : f x ∈ e.source) (he' : f x ∈ e'.source) :
    ContMDiffWithinAt IM 𝓘(𝕜, F) n (fun y ↦ (e' (f y)).2) s x := by
  rw [Trivialization.mem_source] at he he'
  refine (hp.coordChange hf he he').congr_of_eventuallyEq ?_ (by simp [he])
  filter_upwards [hp.continuousWithinAt (e.open_baseSet.mem_nhds he)] with y hy
  simp_all
/-
**Bundle.Trivialization.contMDiffWithinAt_snd_comp_iff** 是 Mathlib 中的一个定理，位于命名空间
 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Bundle.Trivialization.contMDiffWithinAt_snd_comp_iff₂ {f : M → TotalSpace F E}
    (hp : ContMDiffWithinAt IM IB n (π F E ∘ f) s x)
    (he : f x ∈ e.source) (he' : f x ∈ e'.source) :
    ContMDiffWithinAt IM 𝓘(𝕜, F) n (fun y ↦ (e (f y)).2) s x ↔
      ContMDiffWithinAt IM 𝓘(𝕜, F) n (fun y ↦ (e' (f y)).2) s x :=
  ⟨(hp.change_section_trivialization · he he'), (hp.change_section_trivialization · he' he)⟩

end ContMDiffCoordChange

variable [IsManifold IB n B] in
/-- For a `C^n` vector bundle `E` over `B` with fiber modelled on `F`, the change-of-co-ordinates
between two trivializations `e`, `e'` for `E`, considered as charts to `B × F`, is `C^n` and
fiberwise linear. -/
/-
**ContMDiffFiberwiseLinear.hasGroupoid** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ContMDiffFiberwiseLinear.hasGroupoid : HasGroupoid (TotalSpace F E) (contM
DiffFiberwiseLinear B F IB n) where compatible
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContMDiffOn.continuousOn`：ContMDiffOn.continuousOn (hf : ContMDiffOn I I
' n f s) : ContinuousOn f s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_contMDiffFiberwiseLinear_iff`：mem_contMDiffFiberwiseLinear_iff {n : 
Nat∞ω} (e : OpenPartialHomeomorph (B × F) (B × F)) : e in contMDiffFiberwiseLine
ar B F IB n ↔ exists (…
· 使用定理 `trivialization_linear`：∀ (R : Type u_1) {B : Type u_2} {F : Type u_3} {E
 : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x : B) → AddCom
mMonoid (E …
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
· 使用定理 `Bundle.Trivialization.open_baseSet`：∀ {B : Type u_1} {F : Type u_2} {Z :
 Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 :
 TopologicalSpace Z] {pr…
· 使用定理 `contMDiffOn_coordChangeL`：contMDiffOn_coordChangeL : ContMDiffOn IB 𝓘(𝕜,
 F ->L[𝕜] F) n (fun b : B => (e.coordChangeL 𝕜 e' b : F ->L[𝕜] F)) (e.baseSet in
ter e'.baseSet…
· 使用定理 `contMDiffOn_symm_coordChangeL`：contMDiffOn_symm_coordChangeL : ContMDiff
On IB 𝓘(𝕜, F ->L[𝕜] F) n (fun b : B => ((e.coordChangeL 𝕜 e' b).symm : F ->L[𝕜] 
F)) (e.baseSet inte…
· 使用定理 `Setoid.symm`：∀ {α : Sort u} [inst : Setoid α] {a b : α}, a ≈ b → b ≈ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Bundle.Trivialization.symm_trans_source_eq`：∀ {B : Type u_1} {F : Type u
_2} {Z : Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {pr
oj : Z → B}   [inst_2 : Topologi…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Bundle.Trivialization.apply_symm_apply_eq_coordChangeL`：∀ {R : Type u_1}
 {B : Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : Semiring R] [inst_1 : 
TopologicalSpace F]   [inst_2 : TopologicalS…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
For a `C^n` vector bundle `E` over `B` with fiber modelled on `F`, the change-of
-co-ordinates
between two trivializations `e`, `e'` for `E`, considered as charts to `B × F`, 
is `C^n` and
fiberwise linear.
-/
instance ContMDiffFiberwiseLinear.hasGroupoid :
    HasGroupoid (TotalSpace F E) (contMDiffFiberwiseLinear B F IB n) where
  compatible := by
    rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
    have : MemTrivializationAtlas e := ⟨he⟩
    have : MemTrivializationAtlas e' := ⟨he'⟩
    rw [mem_contMDiffFiberwiseLinear_iff]
    refine ⟨_, _, e.open_baseSet.inter e'.open_baseSet, contMDiffOn_coordChangeL e e',
      contMDiffOn_symm_coordChangeL e e', ?_⟩
    refine OpenPartialHomeomorph.eqOnSourceSetoid.symm ⟨?_, ?_⟩
    · simp only [FiberwiseLinear.openPartialHomeomorph, trans_toPartialEquiv, symm_toPartialEquiv,
        e.symm_trans_source_eq e']
    · rintro ⟨b, v⟩ hb
      exact (e.apply_symm_apply_eq_coordChangeL e' hb.1 v).symm

variable [IsManifold IB n B] in
/-- A `C^n` vector bundle `E` is naturally a `C^n` manifold. -/
/-
**Bundle.TotalSpace.isManifold** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Bundle.TotalSpace.isManifold : IsManifold (IB.prod 𝓘(𝕜, F)) n (TotalSpace 
F E)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.HasGroupoid.comp`：∀ {H₁ : Type u_6} [inst : Topologica
lSpace H₁] {H₂ : Type u_7} [inst_1 : TopologicalSpace H₂] {H₃ : Type u_8}   [ins
t_2 : TopologicalSpace H…
· 使用定理 `IsManifold.toHasGroupoid`：∀ {𝕜 : Type u_1} {inst : NontriviallyNormedFie
ld 𝕜} {E : Type u_2} {inst_1 : NormedAddCommGroup E}   {inst_2 : NormedSpace 𝕜 E
} {H : Type u_…
· 使用定理 `IsManifold.instOfTopWithTopENat`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSp
ace 𝕜 E] {H : Type u_…
· 使用定理 `instClosedUnderRestrictionContDiffGroupoid`：∀ {n : WithTop ℕ∞} {𝕜 : Type
 u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommG
roup E]   [inst_2 : NormedSpace …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContMDiffOn.continuousOn`：ContMDiffOn.continuousOn (hf : ContMDiffOn I I
' n f s) : ContinuousOn f s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_contMDiffFiberwiseLinear_iff`：mem_contMDiffFiberwiseLinear_iff {n : 
Nat∞ω} (e : OpenPartialHomeomorph (B × F) (B × F)) : e in contMDiffFiberwiseLine
ar B F IB n ↔ exists (…
· 使用定理 `isLocalStructomorphOn_contDiffGroupoid_iff`：isLocalStructomorphOn_contDi
ffGroupoid_iff (f : OpenPartialHomeomorph M M') : LiftPropOn (contDiffGroupoid n
 I).IsLocalStructomorphWithinAt …
· 使用定理 `ContMDiffOn.congr`：ContMDiffOn.congr (h : ContMDiffOn I I' n f s) (h₁ : 
forall y in s, f₁ y = f y) : ContMDiffOn I I' n f₁ s
· 使用定理 `OpenPartialHomeomorph.EqOnSource.source_eq`：∀ {X : Type u_1} {Y : Type u
_3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   {e e' : OpenPart
ialHomeomorph X Y}, e ≈ e' → e.s…
· 使用定理 `ContMDiffOn.prodMk`：ContMDiffOn.prodMk {f : M -> M'} {g : M -> N'} (hf :
 ContMDiffOn I I' n f s) (hg : ContMDiffOn I J' n g s) : ContMDiffOn I (I'.prod 
J') n (f…
· 使用定理 `contMDiffOn_fst`：contMDiffOn_fst {s : Set (M × N)} : ContMDiffOn (I.prod
 J) I n Prod.fst s
· 使用定理 `ContMDiffOn.clm_apply`：ContMDiffOn.clm_apply {g : M -> F₁ ->L[𝕜] F₂} {f 
: M -> F₁} {s : Set M} (hg : ContMDiffOn I 𝓘(𝕜, F₁ ->L[𝕜] F₂) n g s) (hf : ContM
DiffOn I 𝓘(…
· 使用定理 `ContMDiffOn.comp`：ContMDiffOn.comp {t : Set M'} {g : M' -> M''} (hg : Co
ntMDiffOn I' I'' n g t) (hf : ContMDiffOn I I' n f s) (st : s subseteq f ⁻¹' t) 
: Cont…
· 使用定理 `Set.prod_subset_preimage_fst`：prod_subset_preimage_fst (s : Set α) (t : 
Set β) : s ×ˢ t subseteq Prod.fst ⁻¹' s
· 使用定理 `contMDiffOn_snd`：contMDiffOn_snd {s : Set (M × N)} : ContMDiffOn (I.prod
 J) J n Prod.snd s
· 使用定理 `OpenPartialHomeomorph.EqOnSource.eqOn`：∀ {X : Type u_1} {Y : Type u_3} [
inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   {e e' : OpenPartialHo
meomorph X Y}, e ≈ e' → Set…
· 使用定理 `OpenPartialHomeomorph.EqOnSource.target_eq`：∀ {X : Type u_1} {Y : Type u
_3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   {e e' : OpenPart
ialHomeomorph X Y}, e ≈ e' → e.t…
· 使用定理 `OpenPartialHomeomorph.EqOnSource.symm'`：∀ {X : Type u_1} {Y : Type u_3} 
[inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   {e e' : OpenPartialH
omeomorph X Y}, e ≈ e' → e.s…

--- 原说明 ---
A `C^n` vector bundle `E` is naturally a `C^n` manifold.
-/
instance Bundle.TotalSpace.isManifold :
    IsManifold (IB.prod 𝓘(𝕜, F)) n (TotalSpace F E) := by
  refine { StructureGroupoid.HasGroupoid.comp (contMDiffFiberwiseLinear B F IB n) ?_ with }
  intro e he
  rw [mem_contMDiffFiberwiseLinear_iff] at he
  obtain ⟨φ, U, hU, hφ, h2φ, heφ⟩ := he
  rw [isLocalStructomorphOn_contDiffGroupoid_iff]
  refine ⟨ContMDiffOn.congr ?_ (EqOnSource.eqOn heφ),
      ContMDiffOn.congr ?_ (EqOnSource.eqOn (EqOnSource.symm' heφ))⟩
  · rw [EqOnSource.source_eq heφ]
    apply contMDiffOn_fst.prodMk
    exact (hφ.comp contMDiffOn_fst <| prod_subset_preimage_fst _ _).clm_apply contMDiffOn_snd
  · rw [EqOnSource.target_eq heφ]
    apply contMDiffOn_fst.prodMk
    exact (h2φ.comp contMDiffOn_fst <| prod_subset_preimage_fst _ _).clm_apply contMDiffOn_snd

section

variable {F E}
variable {e e' : Trivialization F (π F E)} [MemTrivializationAtlas e] [MemTrivializationAtlas e']

namespace Bundle.Trivialization

/-
**Bundle.Trivialization.contMDiffWithinAt_iff** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.
Trivialization`。
形式化陈述：contMDiffWithinAt_iff {f : M -> TotalSpace F E} {s : Set M} {x₀ : M} (he :
 f x₀ in e.source) : ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F)) n f s x₀ ↔ ContMDiff
WithinAt IM IB n (fun x => (f x).proj) s x₀ ∧ ContMDiffWithinAt IM 𝓘(𝕜, F) n (fu
n x => (e (f x)).2) s x₀
参数：he : f x₀ in e.source。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Bundle.contMDiffWithinAt_totalSpace`：contMDiffWithinAt_totalSpace {f : M
 -> TotalSpace F E} {s : Set M} {x₀ : M} : ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F)
) n f s x₀ ↔ ContMDiffWit…
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用定理 `Bundle.Trivialization.contMDiffWithinAt_snd_comp_iff₂`：Bundle.Trivializa
tion.contMDiffWithinAt_snd_comp_iff₂ {f : M -> TotalSpace F E} (hp : ContMDiffWi
thinAt IM IB n (π F E ∘ f) s x) (he : f x i…
· 使用定理 `instMemTrivializationAtlasTrivializationAt`：∀ {B : Type u_2} {F : Type u
_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {E : B → Type u_5}
   [inst_2 : TopologicalSpace (B…
· 使用定理 `FiberBundle.mem_trivializationAt_proj_source`：mem_trivializationAt_proj_
source {x : TotalSpace F E} : x in (trivializationAt F E x.proj).source
-/
theorem contMDiffWithinAt_iff {f : M → TotalSpace F E} {s : Set M} {x₀ : M}
    (he : f x₀ ∈ e.source) :
    ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F)) n f s x₀ ↔
      ContMDiffWithinAt IM IB n (fun x => (f x).proj) s x₀ ∧
      ContMDiffWithinAt IM 𝓘(𝕜, F) n (fun x ↦ (e (f x)).2) s x₀ :=
  contMDiffWithinAt_totalSpace.trans <| and_congr_right fun h ↦
    Trivialization.contMDiffWithinAt_snd_comp_iff₂ h FiberBundle.mem_trivializationAt_proj_source he
/-
**Bundle.Trivialization.contMDiffAt_iff** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Trivia
lization`。
形式化陈述：contMDiffAt_iff {f : M -> TotalSpace F E} {x₀ : M} (he : f x₀ in e.source)
 : ContMDiffAt IM (IB.prod 𝓘(𝕜, F)) n f x₀ ↔ ContMDiffAt IM IB n (fun x => (f x)
.proj) x₀ ∧ ContMDiffAt IM 𝓘(𝕜, F) n (fun x => (e (f x)).2) x₀
参数：he : f x₀ in e.source。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Trivialization.contMDiffWithinAt_iff`：contMDiffWithinAt_iff {f : 
M -> TotalSpace F E} {s : Set M} {x₀ : M} (he : f x₀ in e.source) : ContMDiffWit
hinAt IM (IB.prod 𝓘(𝕜, F)) n f s …
-/
theorem contMDiffAt_iff {f : M → TotalSpace F E} {x₀ : M} (he : f x₀ ∈ e.source) :
    ContMDiffAt IM (IB.prod 𝓘(𝕜, F)) n f x₀ ↔
      ContMDiffAt IM IB n (fun x => (f x).proj) x₀ ∧
      ContMDiffAt IM 𝓘(𝕜, F) n (fun x ↦ (e (f x)).2) x₀ :=
  e.contMDiffWithinAt_iff he
/-
**Bundle.Trivialization.contMDiffOn_iff** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Trivia
lization`。
形式化陈述：contMDiffOn_iff {f : M -> TotalSpace F E} {s : Set M} (he : MapsTo f s e.s
ource) : ContMDiffOn IM (IB.prod 𝓘(𝕜, F)) n f s ↔ ContMDiffOn IM IB n (fun x => 
(f x).proj) s ∧ ContMDiffOn IM 𝓘(𝕜, F) n (fun x => (e (f x)).2) s
参数：he : MapsTo f s e.source。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `Bundle.Trivialization.contMDiffWithinAt_iff`：contMDiffWithinAt_iff {f : 
M -> TotalSpace F E} {s : Set M} {x₀ : M} (he : f x₀ in e.source) : ContMDiffWit
hinAt IM (IB.prod 𝓘(𝕜, F)) n f s …
-/
theorem contMDiffOn_iff {f : M → TotalSpace F E} {s : Set M}
    (he : MapsTo f s e.source) :
    ContMDiffOn IM (IB.prod 𝓘(𝕜, F)) n f s ↔
      ContMDiffOn IM IB n (fun x => (f x).proj) s ∧
      ContMDiffOn IM 𝓘(𝕜, F) n (fun x ↦ (e (f x)).2) s := by
  simp only [ContMDiffOn, ← forall_and]
  exact forall₂_congr fun x hx ↦ e.contMDiffWithinAt_iff (he hx)
/-
**Bundle.Trivialization.contMDiff_iff** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Triviali
zation`。
形式化陈述：contMDiff_iff {f : M -> TotalSpace F E} (he : forall x, f x in e.source) :
 ContMDiff IM (IB.prod 𝓘(𝕜, F)) n f ↔ ContMDiff IM IB n (fun x => (f x).proj) ∧ 
ContMDiff IM 𝓘(𝕜, F) n (fun x => (e (f x)).2)
参数：he : forall x, f x in e.source。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `Bundle.Trivialization.contMDiffAt_iff`：contMDiffAt_iff {f : M -> TotalSp
ace F E} {x₀ : M} (he : f x₀ in e.source) : ContMDiffAt IM (IB.prod 𝓘(𝕜, F)) n f
 x₀ ↔ ContMDiffAt IM IB n (…
· 使用定理 `forall_and`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (x : α), p x ∧ q x) ↔ 
(∀ (x : α), p x) ∧ ∀ (x : α), q x
-/
theorem contMDiff_iff {f : M → TotalSpace F E} (he : ∀ x, f x ∈ e.source) :
    ContMDiff IM (IB.prod 𝓘(𝕜, F)) n f ↔
      ContMDiff IM IB n (fun x => (f x).proj) ∧
      ContMDiff IM 𝓘(𝕜, F) n (fun x ↦ (e (f x)).2) :=
  (forall_congr' fun x ↦ e.contMDiffAt_iff (he x)).trans forall_and
/-
**Bundle.Trivialization.contMDiffOn** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Trivializa
tion`。
形式化陈述：contMDiffOn (e : Trivialization F (π F E)) [MemTrivializationAtlas e] : Co
ntMDiffOn (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) n e e.source
参数：e : Trivialization F (π F E)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contMDiffOn_id`：contMDiffOn_id : ContMDiffOn I I n (id : M -> M) s
· 使用定理 `ContMDiffOn.congr`：ContMDiffOn.congr (h : ContMDiffOn I I' n f s) (h₁ : 
forall y in s, f₁ y = f y) : ContMDiffOn I I' n f₁ s
· 使用定理 `ContMDiffOn.prodMk`：ContMDiffOn.prodMk {f : M -> M'} {g : M -> N'} (hf :
 ContMDiffOn I I' n f s) (hg : ContMDiffOn I J' n g s) : ContMDiffOn I (I'.prod 
J') n (f…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.Trivialization.contMDiffOn_iff`：contMDiffOn_iff {f : M -> TotalSp
ace F E} {s : Set M} (he : MapsTo f s e.source) : ContMDiffOn IM (IB.prod 𝓘(𝕜, F
)) n f s ↔ ContMDiffOn IM I…
· 使用定理 `Set.mapsTo_id`：mapsTo_id (s : Set α) : MapsTo id s s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Bundle.Trivialization.mk_proj_snd`：∀ {B : Type u_1} {F : Type u_2} {Z : 
Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z → 
B}   [inst_2 : Topologi…
-/
theorem contMDiffOn (e : Trivialization F (π F E)) [MemTrivializationAtlas e] :
    ContMDiffOn (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) n e e.source := by
  have : ContMDiffOn (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) n id e.source := contMDiffOn_id
  rw [e.contMDiffOn_iff (mapsTo_id _)] at this
  exact (this.1.prodMk this.2).congr fun x hx ↦ (e.mk_proj_snd hx).symm
/-
**Bundle.Trivialization.contMDiffOn_symm** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Trivi
alization`。
形式化陈述：contMDiffOn_symm (e : Trivialization F (π F E)) [MemTrivializationAtlas e]
 : ContMDiffOn (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) n e.toOpenPartialHomeomorph.s
ymm e.target
参数：e : Trivialization F (π F E)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.Trivialization.contMDiffOn_iff`：contMDiffOn_iff {f : M -> TotalSp
ace F E} {s : Set M} (he : MapsTo f s e.source) : ContMDiffOn IM (IB.prod 𝓘(𝕜, F
)) n f s ↔ ContMDiffOn IM I…
· 使用定理 `OpenPartialHomeomorph.mapsTo_symm`：∀ {X : Type u_1} {Y : Type u_3} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomorp
h X Y), Set.MapsTo (↑e.…
· 使用定理 `ContMDiffOn.congr`：ContMDiffOn.congr (h : ContMDiffOn I I' n f s) (h₁ : 
forall y in s, f₁ y = f y) : ContMDiffOn I I' n f₁ s
· 使用定理 `contMDiffOn_fst`：contMDiffOn_fst {s : Set (M × N)} : ContMDiffOn (I.prod
 J) I n Prod.fst s
· 使用定理 `Bundle.Trivialization.proj_symm_apply`：∀ {B : Type u_1} {F : Type u_2} {
Z : Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : 
Z → B}   [inst_2 : Topologi…
· 使用定理 `contMDiffOn_snd`：contMDiffOn_snd {s : Set (M × N)} : ContMDiffOn (I.prod
 J) J n Prod.snd s
· 使用定理 `Bundle.Trivialization.apply_symm_apply`：∀ {B : Type u_1} {F : Type u_2} 
{Z : Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj :
 Z → B}   [inst_2 : Topologi…
-/
theorem contMDiffOn_symm (e : Trivialization F (π F E)) [MemTrivializationAtlas e] :
    ContMDiffOn (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) n e.toOpenPartialHomeomorph.symm e.target := by
  rw [e.contMDiffOn_iff e.toOpenPartialHomeomorph.mapsTo_symm]
  refine ⟨contMDiffOn_fst.congr fun x hx ↦ e.proj_symm_apply hx,
    contMDiffOn_snd.congr fun x hx ↦ ?_⟩
  rw [e.apply_symm_apply hx]

/-- Smoothness of a `C^n` section at `x₀` within a set `a` can be determined
using any trivialisation whose `baseSet` contains `x₀`. -/
/-
**Bundle.Trivialization.contMDiffWithinAt_section** 是 Mathlib 中的一个定理，位于命名空间 `Bun
dle.Trivialization`。
形式化陈述：contMDiffWithinAt_section {s : forall x, E x} (a : Set B) {x₀ : B} {e : Tr
ivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F E -> B)} [MemTrivia
lizationAtlas e] (hx₀ : x₀ in e.baseSet) : ContMDiffWithinAt IB (IB.prod 𝓘(𝕜, F)
) n (fun x => TotalSpace.mk' F x (s x)) a x₀ ↔ ContMDiffWithinAt IB 𝓘(𝕜, F) n (f
un x => (e ⟨x, s x⟩).2) a x₀
参数：a : Set B；Bundle.TotalSpace.proj : Bundle.TotalSpace F E -> B；hx₀ : x₀ in e.b
aseSet。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.Trivialization.contMDiffWithinAt_iff`：contMDiffWithinAt_iff {f : 
M -> TotalSpace F E} {s : Set M} {x₀ : M} (he : f x₀ in e.source) : ContMDiffWit
hinAt IM (IB.prod 𝓘(𝕜, F)) n f s …
· 使用定理 `Bundle.Trivialization.mem_source`：∀ {B : Type u_1} {F : Type u_2} {Z : T
ype u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z → B
}   [inst_2 : Topologi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Smoothness of a `C^n` section at `x₀` within a set `a` can be determined
using any trivialisation whose `baseSet` contains `x₀`.
-/
theorem contMDiffWithinAt_section {s : ∀ x, E x} (a : Set B) {x₀ : B}
    {e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F E → B)}
    [MemTrivializationAtlas e] (hx₀ : x₀ ∈ e.baseSet) :
    ContMDiffWithinAt IB (IB.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (s x)) a x₀ ↔
      ContMDiffWithinAt IB 𝓘(𝕜, F) n (fun x ↦ (e ⟨x, s x⟩).2) a x₀ := by
  rw [e.contMDiffWithinAt_iff]
  · change ContMDiffWithinAt IB IB n id a x₀ ∧ _ ↔ _
    simp [contMDiffWithinAt_id]
  · rwa [mem_source]

/-- Smoothness of a `C^n` section at `x₀` can be determined
using any trivialisation whose `baseSet` contains `x₀`. -/
/-
**Bundle.Trivialization.contMDiffAt_section_iff** 是 Mathlib 中的一个定理，位于命名空间 `Bundl
e.Trivialization`。
形式化陈述：contMDiffAt_section_iff {s : forall x, E x} {x₀ : B} (e : Trivialization F
 (Bundle.TotalSpace.proj : Bundle.TotalSpace F E -> B)) [MemTrivializationAtlas 
e] (hx₀ : x₀ in e.baseSet) : ContMDiffAt IB (IB.prod 𝓘(𝕜, F)) n (fun x => TotalS
pace.mk' F x (s x)) x₀ ↔ ContMDiffAt IB 𝓘(𝕜, F) n (fun x => (e ⟨x, s x⟩).2) x₀
参数：e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F E -> B)；hx
₀ : x₀ in e.baseSet。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.Trivialization.contMDiffWithinAt_section`：contMDiffWithinAt_secti
on {s : forall x, E x} (a : Set B) {x₀ : B} {e : Trivialization F (Bundle.TotalS
pace.proj : Bundle.TotalSpace F E -> …

--- 原说明 ---
Smoothness of a `C^n` section at `x₀` can be determined
using any trivialisation whose `baseSet` contains `x₀`.
-/
theorem contMDiffAt_section_iff {s : ∀ x, E x} {x₀ : B}
    (e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F E → B))
    [MemTrivializationAtlas e] (hx₀ : x₀ ∈ e.baseSet) :
    ContMDiffAt IB (IB.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (s x)) x₀ ↔
      ContMDiffAt IB 𝓘(𝕜, F) n (fun x ↦ (e ⟨x, s x⟩).2) x₀ := by
  simp_rw [← contMDiffWithinAt_univ]
  exact e.contMDiffWithinAt_section univ hx₀

/-- Smoothness of a `C^n` section on `s` can be determined
using any trivialisation whose `baseSet` contains `s`. -/
/-
**Bundle.Trivialization.contMDiffOn_section_iff** 是 Mathlib 中的一个定理，位于命名空间 `Bundl
e.Trivialization`。
形式化陈述：contMDiffOn_section_iff {s : forall x, E x} {a : Set B} (e : Trivializatio
n F (Bundle.TotalSpace.proj : Bundle.TotalSpace F E -> B)) [MemTrivializationAtl
as e] (ha : IsOpen a) (ha' : a subseteq e.baseSet) : ContMDiffOn IB (IB.prod 𝓘(𝕜
, F)) n (fun x => TotalSpace.mk' F x (s x)) a ↔ ContMDiffOn IB 𝓘(𝕜, F) n (fun x 
=> (e ⟨x, s x⟩).2) a
参数：e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F E -> B)；ha
 : IsOpen a；ha' : a subseteq e.baseSet。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffWithinAt.contMDiffAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {H : Type u_…
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `ContMDiffAt.contMDiffWithinAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {H : Type u_…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Bundle.Trivialization.contMDiffAt_section_iff`：contMDiffAt_section_iff {
s : forall x, E x} {x₀ : B} (e : Trivialization F (Bundle.TotalSpace.proj : Bund
le.TotalSpace F E -> B)) [MemTrivia…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a

--- 原说明 ---
Smoothness of a `C^n` section on `s` can be determined
using any trivialisation whose `baseSet` contains `s`.
-/
theorem contMDiffOn_section_iff {s : ∀ x, E x} {a : Set B}
    (e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F E → B))
    [MemTrivializationAtlas e] (ha : IsOpen a) (ha' : a ⊆ e.baseSet) :
    ContMDiffOn IB (IB.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (s x)) a ↔
      ContMDiffOn IB 𝓘(𝕜, F) n (fun x ↦ (e ⟨x, s x⟩).2) a := by
  refine ⟨fun h x hx ↦ ?_, fun h x hx ↦ ?_⟩ <;>
  have := (h x hx).contMDiffAt <| ha.mem_nhds hx
  · exact ((e.contMDiffAt_section_iff (ha' hx)).mp this).contMDiffWithinAt
  · exact ((e.contMDiffAt_section_iff (ha' hx)).mpr this).contMDiffWithinAt

/-- For any trivialization `e`, the smoothness of a `C^n` section on `e.baseSet`
can be determined using `e`. -/
/-
**Bundle.Trivialization.contMDiffOn_section_baseSet_iff** 是 Mathlib 中的一个定理，位于命名空
间 `Bundle.Trivialization`。
形式化陈述：contMDiffOn_section_baseSet_iff {s : forall x, E x} (e : Trivialization F 
(Bundle.TotalSpace.proj : Bundle.TotalSpace F E -> B)) [MemTrivializationAtlas e
] : ContMDiffOn IB (IB.prod 𝓘(𝕜, F)) n (fun x => TotalSpace.mk' F x (s x)) e.bas
eSet ↔ ContMDiffOn IB 𝓘(𝕜, F) n (fun x => (e ⟨x, s x⟩).2) e.baseSet
参数：e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F E -> B)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Trivialization.contMDiffOn_section_iff`：contMDiffOn_section_iff {
s : forall x, E x} {a : Set B} (e : Trivialization F (Bundle.TotalSpace.proj : B
undle.TotalSpace F E -> B)) [MemTri…
· 使用定理 `Bundle.Trivialization.open_baseSet`：∀ {B : Type u_1} {F : Type u_2} {Z :
 Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 :
 TopologicalSpace Z] {pr…
· 使用定理 `subset_rfl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorde
r α] {a : α}, a ⊆ a

--- 原说明 ---
For any trivialization `e`, the smoothness of a `C^n` section on `e.baseSet`
can be determined using `e`.
-/
theorem contMDiffOn_section_baseSet_iff {s : ∀ x, E x}
    (e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F E → B))
    [MemTrivializationAtlas e] :
    ContMDiffOn IB (IB.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (s x)) e.baseSet ↔
      ContMDiffOn IB 𝓘(𝕜, F) n (fun x ↦ (e ⟨x, s x⟩).2) e.baseSet :=
  e.contMDiffOn_section_iff e.open_baseSet subset_rfl

end Bundle.Trivialization

end

/-! ### Core construction for `C^n` vector bundles -/

namespace VectorBundleCore

variable {F}
variable {ι : Type*} (Z : VectorBundleCore 𝕜 B F ι)

/-- Mixin for a `VectorBundleCore` stating that transition functions are `C^n`. -/
/-
**VectorBundleCore.IsContMDiff** 是 Mathlib 中的一个归纳类型，位于命名空间 `VectorBundleCore`。
形式化陈述：{𝕜 : Type u_1} →   {B : Type u_2} →     {F : Type u_4} →       [inst : Non
triviallyNormedField 𝕜] →         {EB : Type u_7} →           [inst_1 : NormedAd
dCommGroup EB] →             [inst_2 : NormedSpace 𝕜 EB] →               {HB : T
ype u_8} →                 [inst_3 : TopologicalSpace HB] →                   [i
nst_4 : TopologicalSpace B] →                     [ChartedSpace HB B] →         
              [inst_6 : NormedAddCommGroup F] →                         [inst_7 
: NormedSpace 𝕜 F] →                           {ι : Type u_11} → VectorBundleCor
e 𝕜 B F ι → ModelWithCorners 𝕜 EB HB → WithTop ℕ∞ → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Mixin for a `VectorBundleCore` stating that transition functions are `C^n`.
-/
class IsContMDiff (IB : ModelWithCorners 𝕜 EB HB) (n : ℕ∞ω) : Prop where
  contMDiffOn_coordChange :
    ∀ i j, ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] F) n (Z.coordChange i j) (Z.baseSet i ∩ Z.baseSet j)
/-
**VectorBundleCore.contMDiffOn_coordChange** 是 Mathlib 中的一个定理，位于命名空间 `VectorBund
leCore`。
形式化陈述：contMDiffOn_coordChange (IB : ModelWithCorners 𝕜 EB HB) [h : Z.IsContMDiff
 IB n] (i j : ι) : ContMDiffOn IB 𝓘(𝕜, F ->L[𝕜] F) n (Z.coordChange i j) (Z.base
Set i inter Z.baseSet j)
参数：IB : ModelWithCorners 𝕜 EB HB；i j : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `VectorBundleCore.IsContMDiff.contMDiffOn_coordChange`：∀ {𝕜 : Type u_1} {
B : Type u_2} {F : Type u_4} {inst : NontriviallyNormedField 𝕜} {EB : Type u_7} 
  {inst_1 : NormedAddCommGroup EB} {inst_2…
-/
theorem contMDiffOn_coordChange (IB : ModelWithCorners 𝕜 EB HB) [h : Z.IsContMDiff IB n] (i j : ι) :
    ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] F) n (Z.coordChange i j) (Z.baseSet i ∩ Z.baseSet j) :=
  h.1 i j

variable [Z.IsContMDiff IB n]

/-- If a `VectorBundleCore` has the `IsContMDiff` mixin, then the vector bundle constructed from it
is a `C^n` vector bundle. -/
/-
**VectorBundleCore.instContMDiffVectorBundle** 是 Mathlib 中的一个实例，位于命名空间 `VectorBu
ndleCore`。
形式化陈述：instContMDiffVectorBundle : ContMDiffVectorBundle n F Z.Fiber IB where con
tMDiffOn_coordChangeL
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `VectorBundleCore.vectorBundle`：∀ {R : Type u_1} {B : Type u_2} {F : Type
 u_3} [inst : NontriviallyNormedField R] [inst_1 : NormedAddCommGroup F]   [inst
_2 : NormedSpace R …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `trivialization_linear`：∀ (R : Type u_1) {B : Type u_2} {F : Type u_3} {E
 : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x : B) → AddCom
mMonoid (E …
· 使用定理 `ContMDiffOn.congr`：ContMDiffOn.congr (h : ContMDiffOn I I' n f s) (h₁ : 
forall y in s, f₁ y = f y) : ContMDiffOn I I' n f₁ s
· 使用定理 `VectorBundleCore.contMDiffOn_coordChange`：contMDiffOn_coordChange (IB : 
ModelWithCorners 𝕜 EB HB) [h : Z.IsContMDiff IB n] (i j : ι) : ContMDiffOn IB 𝓘(
𝕜, F ->L[𝕜] F) n (Z.coordChang…
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `VectorBundleCore.localTriv_coordChange_eq`：∀ {R : Type u_1} {B : Type u_
2} {F : Type u_3} [inst : NontriviallyNormedField R] [inst_1 : NormedAddCommGrou
p F]   [inst_2 : NormedSpace R …

--- 原说明 ---
If a `VectorBundleCore` has the `IsContMDiff` mixin, then the vector bundle cons
tructed from it
is a `C^n` vector bundle.
-/
instance instContMDiffVectorBundle : ContMDiffVectorBundle n F Z.Fiber IB where
  contMDiffOn_coordChangeL := by
    rintro - - ⟨i, rfl⟩ ⟨i', rfl⟩
    refine (Z.contMDiffOn_coordChange IB i i').congr fun b hb ↦ ?_
    ext v
    exact Z.localTriv_coordChange_eq i i' hb v

end VectorBundleCore

/-! ### The trivial `C^n` vector bundle -/

/-- A trivial vector bundle over a manifold is a `C^n` vector bundle. -/
/-
**Bundle.Trivial.contMDiffVectorBundle** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Bundle.Trivial.contMDiffVectorBundle : ContMDiffVectorBundle n F (Bundle.T
rivial B F) IB where contMDiffOn_coordChangeL
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `trivialization_linear`：∀ (R : Type u_1) {B : Type u_2} {F : Type u_3} {E
 : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x : B) → AddCom
mMonoid (E …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Bundle.Trivial.trivialization.coordChangeL`：∀ {𝕜 : Type u_1} (B : Type u
_2) (F : Type u_3) [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGro
up F]   [inst_2 : NormedSpace 𝕜 …
· 使用定理 `ContMDiff.contMDiffOn`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
H : Type u_…
· 使用定理 `contMDiff_const`：contMDiff_const : ContMDiff I I' n fun _ : M => c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Bundle.Trivial.eq_trivialization`：eq_trivialization (e : Trivialization 
F (π F (Bundle.Trivial B F))) [i : MemTrivializationAtlas e] : e = trivializatio
n B F

--- 原说明 ---
A trivial vector bundle over a manifold is a `C^n` vector bundle.
-/
instance Bundle.Trivial.contMDiffVectorBundle :
    ContMDiffVectorBundle n F (Bundle.Trivial B F) IB where
  contMDiffOn_coordChangeL := by
    intro e e' he he'
    obtain rfl := Bundle.Trivial.eq_trivialization B F e
    obtain rfl := Bundle.Trivial.eq_trivialization B F e'
    simp_rw [Bundle.Trivial.trivialization.coordChangeL]
    exact contMDiff_const.contMDiffOn

/-! ### Direct sums of `C^n` vector bundles -/


section Prod

variable (F₁ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] (E₁ : B → Type*)
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, AddCommMonoid (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]

variable (F₂ : Type*) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] (E₂ : B → Type*)
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, AddCommMonoid (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]

variable [∀ x : B, TopologicalSpace (E₁ x)] [∀ x : B, TopologicalSpace (E₂ x)] [FiberBundle F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₁ E₁] [VectorBundle 𝕜 F₂ E₂]
  [ContMDiffVectorBundle n F₁ E₁ IB] [ContMDiffVectorBundle n F₂ E₂ IB]

variable [IsManifold IB n B]

/-- The direct sum of two `C^n` vector bundles over the same base is a `C^n` vector bundle. -/
/-
**Bundle.Prod.contMDiffVectorBundle** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Bundle.Prod.contMDiffVectorBundle : ContMDiffVectorBundle n (F₁ × F₂) (E₁ 
×ᵇ E₂) IB where contMDiffOn_coordChangeL
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `trivialization_linear`：∀ (R : Type u_1) {B : Type u_2} {F : Type u_3} {E
 : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x : B) → AddCom
mMonoid (E …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContMDiffOn.congr`：ContMDiffOn.congr (h : ContMDiffOn I I' n f s) (h₁ : 
forall y in s, f₁ y = f y) : ContMDiffOn I I' n f₁ s
· 使用定理 `ContMDiffOn.clm_prodMap`：ContMDiffOn.clm_prodMap {g : M -> F₁ ->L[𝕜] F₃}
 {f : M -> F₂ ->L[𝕜] F₄} {s : Set M} (hg : ContMDiffOn I 𝓘(𝕜, F₁ ->L[𝕜] F₃) n g 
s) (hf : Cont…
· 使用定理 `ContMDiffOn.mono`：ContMDiffOn.mono (hf : ContMDiffOn I I' n f s) (hts : 
t subseteq s) : ContMDiffOn I I' n f t
· 使用定理 `contMDiffOn_coordChangeL`：contMDiffOn_coordChangeL : ContMDiffOn IB 𝓘(𝕜,
 F ->L[𝕜] F) n (fun b : B => (e.coordChangeL 𝕜 e' b : F ->L[𝕜] F)) (e.baseSet in
ter e'.baseSet…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Bundle.Trivialization.prod_baseSet`：∀ {B : Type u_1} [inst : Topological
Space B] {F₁ : Type u_2} [inst_1 : TopologicalSpace F₁] {E₁ : B → Type u_3}   [i
nst_2 : TopologicalSpace…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Bundle.Trivialization.coordChangeL_prod`：coordChangeL_prod [e₁.IsLinear 
𝕜] [e₁'.IsLinear 𝕜] [e₂.IsLinear 𝕜] [e₂'.IsLinear 𝕜] ⦃b⦄ (hb : (b in e₁.baseSet 
∧ b in e₂.baseSet) ∧ b in e₁'…

--- 原说明 ---
The direct sum of two `C^n` vector bundles over the same base is a `C^n` vector 
bundle.
-/
instance Bundle.Prod.contMDiffVectorBundle : ContMDiffVectorBundle n (F₁ × F₂) (E₁ ×ᵇ E₂) IB where
  contMDiffOn_coordChangeL := by
    rintro _ _ ⟨e₁, e₂, i₁, i₂, rfl⟩ ⟨e₁', e₂', i₁', i₂', rfl⟩
    refine ContMDiffOn.congr ?_ (e₁.coordChangeL_prod 𝕜 e₁' e₂ e₂')
    refine ContMDiffOn.clm_prodMap ?_ ?_
    · refine (contMDiffOn_coordChangeL e₁ e₁').mono ?_
      simp only [Trivialization.prod_baseSet, mfld_simps]
      mfld_set_tac
    · refine (contMDiffOn_coordChangeL e₂ e₂').mono ?_
      simp only [Trivialization.prod_baseSet, mfld_simps]
      mfld_set_tac

end Prod

end WithTopology

/-! ### Prebundle construction for `C^n` vector bundles -/

namespace VectorPrebundle

variable [∀ x, TopologicalSpace (E x)]

variable (IB) in
/-- Mixin for a `VectorPrebundle` stating that coordinate changes are `C^n`. -/
/-
**VectorPrebundle.IsContMDiff** 是 Mathlib 中的一个归纳类型，位于命名空间 `VectorPrebundle`。
形式化陈述：{𝕜 : Type u_1} →   {B : Type u_2} →     {F : Type u_4} →       {E : B → Ty
pe u_6} →         [inst : NontriviallyNormedField 𝕜] →           {EB : Type u_7}
 →             [inst_1 : NormedAddCommGroup EB] →               [inst_2 : Normed
Space 𝕜 EB] →                 {HB : Type u_8} →                   [inst_3 : Topo
logicalSpace HB] →                     ModelWithCorners 𝕜 EB HB →               
        [inst_4 : TopologicalSpace B] →                         [ChartedSpace HB
 B] →                           [inst_6 : (x : B) → AddCommMonoid (E x)] →      
                       [inst_7 : (x : B) → _root_.Module 𝕜 (E x)] →             
                  [inst_8 : NormedAddCommGroup F] →                             
    [inst_9 : NormedSpace 𝕜 F] →                                   [inst_10 : (x
 : B) → TopologicalSpace (E x)] →                                     VectorPreb
undle 𝕜 F E → WithTop ℕ∞ → Prop
参数：x : B；E x；x : B；E x；x : B；E x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Mixin for a `VectorPrebundle` stating that coordinate changes are `C^n`.
-/
class IsContMDiff (a : VectorPrebundle 𝕜 F E) (n : ℕ∞ω) : Prop where
  exists_contMDiffCoordChange :
    ∀ᵉ (e ∈ a.pretrivializationAtlas) (e' ∈ a.pretrivializationAtlas),
      ∃ f : B → F →L[𝕜] F,
        ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] F) n f (e.baseSet ∩ e'.baseSet) ∧
          ∀ (b : B) (_ : b ∈ e.baseSet ∩ e'.baseSet) (v : F),
            f b v = (e' ⟨b, e.symm b v⟩).2

variable (a : VectorPrebundle 𝕜 F E) [ha : a.IsContMDiff IB n] {e e' : Pretrivialization F (π F E)}

variable (IB n) in
/-- A randomly chosen coordinate change on a `VectorPrebundle` satisfying `IsContMDiff`, given by
  the field `exists_coordChange`. Note that `a.contMDiffCoordChange` need not be the same as
  `a.coordChange`. -/
/-
**VectorPrebundle.contMDiffCoordChange** 是 Mathlib 中的一个定义，位于命名空间 `VectorPrebundl
e`。
形式化陈述：(n : WithTop ℕ∞) →   {𝕜 : Type u_1} →     {B : Type u_2} →       {F : Type
 u_4} →         {E : B → Type u_6} →           [inst : NontriviallyNormedField 𝕜
] →             {EB : Type u_7} →               [inst_1 : NormedAddCommGroup EB]
 →                 [inst_2 : NormedSpace 𝕜 EB] →                   {HB : Type u_
8} →                     [inst_3 : TopologicalSpace HB] →                       
(IB : ModelWithCorners 𝕜 EB HB) →                         [inst_4 : TopologicalS
pace B] →                           [inst_5 : ChartedSpace HB B] →              
               [inst_6 : (x : B) → AddCommMonoid (E x)] →                       
        [inst_7 : (x : B) → _root_.Module 𝕜 (E x)] →                            
     [inst_8 : NormedAddCommGroup F] →                                   [inst_9
 : NormedSpace 𝕜 F] →                                     [inst_10 : (x : B) → T
opologicalSpace (E x)] →                                       (a : VectorPrebun
dle 𝕜 F E) →                                         [ha : VectorPrebundle.IsCon
tMDiff IB a n] →                                           {e e' : Bundle.Pretri
vialization F Bundle.TotalSpace.proj} →                                         
    e ∈ a.pretrivializationAtlas → e' ∈ a.pretrivializationAtlas → B → F →L[𝕜] F
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `VectorPrebundle.IsContMDiff.exists_contMDiffCoordChange`：∀ {𝕜 : Type u_1
} {B : Type u_2} {F : Type u_4} {E : B → Type u_6} {inst : NontriviallyNormedFie
ld 𝕜} {EB : Type u_7}   {inst_1 : NormedAddCo…

--- 原说明 ---
A randomly chosen coordinate change on a `VectorPrebundle` satisfying `IsContMDi
ff`, given by
  the field `exists_coordChange`. Note that `a.contMDiffCoordChange` need not be
 the same as
  `a.coordChange`.
-/
@[no_expose] noncomputable def contMDiffCoordChange (he : e ∈ a.pretrivializationAtlas)
    (he' : e' ∈ a.pretrivializationAtlas) (b : B) : F →L[𝕜] F :=
  Classical.choose (ha.exists_contMDiffCoordChange e he e' he') b
/-
**VectorPrebundle.contMDiffOn_contMDiffCoordChange** 是 Mathlib 中的一个定理，位于命名空间 `Ve
ctorPrebundle`。
形式化陈述：contMDiffOn_contMDiffCoordChange (he : e in a.pretrivializationAtlas) (he'
 : e' in a.pretrivializationAtlas) : ContMDiffOn IB 𝓘(𝕜, F ->L[𝕜] F) n (a.contMD
iffCoordChange n IB he he') (e.baseSet inter e'.baseSet)
参数：he : e in a.pretrivializationAtlas；he' : e' in a.pretrivializationAtlas。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `VectorPrebundle.IsContMDiff.exists_contMDiffCoordChange`：∀ {𝕜 : Type u_1
} {B : Type u_2} {F : Type u_4} {E : B → Type u_6} {inst : NontriviallyNormedFie
ld 𝕜} {EB : Type u_7}   {inst_1 : NormedAddCo…
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem contMDiffOn_contMDiffCoordChange (he : e ∈ a.pretrivializationAtlas)
    (he' : e' ∈ a.pretrivializationAtlas) :
    ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] F) n (a.contMDiffCoordChange n IB he he')
      (e.baseSet ∩ e'.baseSet) :=
  (Classical.choose_spec (ha.exists_contMDiffCoordChange e he e' he')).1
/-
**VectorPrebundle.contMDiffCoordChange_apply** 是 Mathlib 中的一个定理，位于命名空间 `VectorPr
ebundle`。
形式化陈述：contMDiffCoordChange_apply (he : e in a.pretrivializationAtlas) (he' : e' 
in a.pretrivializationAtlas) {b : B} (hb : b in e.baseSet inter e'.baseSet) (v :
 F) : a.contMDiffCoordChange n IB he he' b v = (e' ⟨b, e.symm b v⟩).2
参数：he : e in a.pretrivializationAtlas；he' : e' in a.pretrivializationAtlas；hb : 
b in e.baseSet inter e'.baseSet；v : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `VectorPrebundle.IsContMDiff.exists_contMDiffCoordChange`：∀ {𝕜 : Type u_1
} {B : Type u_2} {F : Type u_4} {E : B → Type u_6} {inst : NontriviallyNormedFie
ld 𝕜} {EB : Type u_7}   {inst_1 : NormedAddCo…
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem contMDiffCoordChange_apply (he : e ∈ a.pretrivializationAtlas)
    (he' : e' ∈ a.pretrivializationAtlas) {b : B} (hb : b ∈ e.baseSet ∩ e'.baseSet) (v : F) :
    a.contMDiffCoordChange n IB he he' b v = (e' ⟨b, e.symm b v⟩).2 :=
  (Classical.choose_spec (ha.exists_contMDiffCoordChange e he e' he')).2 b hb v
/-
**VectorPrebundle.mk_contMDiffCoordChange** 是 Mathlib 中的一个定理，位于命名空间 `VectorPrebu
ndle`。
形式化陈述：mk_contMDiffCoordChange (he : e in a.pretrivializationAtlas) (he' : e' in 
a.pretrivializationAtlas) {b : B} (hb : b in e.baseSet inter e'.baseSet) (v : F)
 : (b, a.contMDiffCoordChange n IB he he' b v) = e' ⟨b, e.symm b v⟩
参数：he : e in a.pretrivializationAtlas；he' : e' in a.pretrivializationAtlas；hb : 
b in e.baseSet inter e'.baseSet；v : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.Pretrivialization.mk_symm`：mk_symm (e : Pretrivialization F (π F 
E)) {b : B} (hb : b in e.baseSet) (y : F) : TotalSpace.mk b (e.symm b y) = e.toP
artialEquiv.symm (b, y…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Bundle.Pretrivialization.coe_fst'`：coe_fst' (ex : proj x in e.baseSet) :
 (e x).1 = proj x
· 使用定理 `Bundle.Pretrivialization.proj_symm_apply'`：proj_symm_apply' {b : B} {x :
 F} (hx : b in e.baseSet) : proj (e.toPartialEquiv.symm (b, x)) = b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `VectorPrebundle.contMDiffCoordChange_apply`：contMDiffCoordChange_apply (
he : e in a.pretrivializationAtlas) (he' : e' in a.pretrivializationAtlas) {b : 
B} (hb : b in e.baseSet inter e'…
-/
theorem mk_contMDiffCoordChange (he : e ∈ a.pretrivializationAtlas)
    (he' : e' ∈ a.pretrivializationAtlas) {b : B} (hb : b ∈ e.baseSet ∩ e'.baseSet) (v : F) :
    (b, a.contMDiffCoordChange n IB he he' b v) = e' ⟨b, e.symm b v⟩ := by
  ext
  · rw [e.mk_symm hb.1 v, e'.coe_fst', e.proj_symm_apply' hb.1]
    rw [e.proj_symm_apply' hb.1]; exact hb.2
  · exact a.contMDiffCoordChange_apply he he' hb v

variable (IB) in
/-- Make a `ContMDiffVectorBundle` from a `ContMDiffVectorPrebundle`. -/
/-
**VectorPrebundle.contMDiffVectorBundle** 是 Mathlib 中的一个定理，位于命名空间 `VectorPrebund
le`。
形式化陈述：contMDiffVectorBundle : @ContMDiffVectorBundle n _ _ F E _ _ _ _ _ _ IB _ 
_ _ _ _ _ a.totalSpaceTopology _ a.toFiberBundle a.toVectorBundle
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `VectorPrebundle.toVectorBundle`：∀ {R : Type u_1} {B : Type u_2} {F : Typ
e u_3} {E : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x : B)
 → AddCommMonoid (E …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `trivialization_linear`：∀ (R : Type u_1) {B : Type u_2} {F : Type u_3} {E
 : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x : B) → AddCom
mMonoid (E …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContMDiffOn.congr`：ContMDiffOn.congr (h : ContMDiffOn I I' n f s) (h₁ : 
forall y in s, f₁ y = f y) : ContMDiffOn I I' n f₁ s
· 使用定理 `VectorPrebundle.contMDiffOn_contMDiffCoordChange`：contMDiffOn_contMDiffC
oordChange (he : e in a.pretrivializationAtlas) (he' : e' in a.pretrivialization
Atlas) : ContMDiffOn IB 𝓘(𝕜, F ->L[𝕜] …
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `VectorPrebundle.contMDiffCoordChange_apply`：contMDiffCoordChange_apply (
he : e in a.pretrivializationAtlas) (he' : e' in a.pretrivializationAtlas) {b : 
B} (hb : b in e.baseSet inter e'…
· 使用定理 `ContinuousLinearEquiv.coe_coe`：coe_coe (e : M₁ ≃SL[σ₁₂] M₂) : ⇑(e : M₁ -
>SL[σ₁₂] M₂) = e
· 使用定理 `Bundle.Trivialization.coordChangeL_apply`：∀ {R : Type u_1} {B : Type u_2
} {F : Type u_3} {E : B → Type u_4} [inst : Semiring R] [inst_1 : TopologicalSpa
ce F]   [inst_2 : TopologicalS…

--- 原说明 ---
Make a `ContMDiffVectorBundle` from a `ContMDiffVectorPrebundle`.
-/
theorem contMDiffVectorBundle : @ContMDiffVectorBundle n
    _ _ F E _ _ _ _ _ _ IB _ _ _ _ _ _ a.totalSpaceTopology _ a.toFiberBundle a.toVectorBundle :=
  letI := a.totalSpaceTopology; letI := a.toFiberBundle; letI := a.toVectorBundle
  { contMDiffOn_coordChangeL := by
      rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
      refine (a.contMDiffOn_contMDiffCoordChange he he').congr ?_
      intro b hb
      ext v
      rw [a.contMDiffCoordChange_apply he he' hb v, ContinuousLinearEquiv.coe_coe,
        Trivialization.coordChangeL_apply]
      exacts [rfl, hb] }

end VectorPrebundle

