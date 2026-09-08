/-
Copyright (c) 2025 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.Instances.Icc
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.MeasureTheory.Function.JacobianOneDim

/-! # Lengths of paths in manifolds

Consider a manifold in which the tangent spaces have an enormed structure. Then one defines
`pathELength γ a b` as the length of the path `γ : ℝ → M` between `a` and `b`, i.e., the integral
of the norm of its derivative on `Icc a b`.

We give several ways to write this quantity (as an integral over `Icc`, or `Ioo`, or the subtype
`Icc`, using either `mfderiv` or `mfderivWithin`).

We show that this notion is invariant under reparameterization by a monotone map, in
`pathELength_comp_of_monotoneOn`.

We define `riemannianEDist x y` as the infimum of the length of `C^1` paths between `x`
and `y`. We prove, in `exists_lt_locally_constant_of_riemannianEDist_lt`, that it is also the
infimum on such paths that are moreover locally constant near their endpoints. Such paths can be
glued while retaining the `C^1` property. We deduce that `riemannianEDist` satisfies the triangle
inequality, in `riemannianEDist_triangle`.

Note that `riemannianEDist x y` could also be named `finslerEDist x y` as we do not require that
the metric comes from an inner product space. However, as all the current applications in mathlib
are to Riemannian spaces we stick with the simpler name. This could be changed when Finsler
manifolds are studied in mathlib.
-/

@[expose] public section

open Set MeasureTheory
open scoped Manifold ENNReal ContDiff Topology

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

namespace Manifold

variable [∀ (x : M), ENorm (TangentSpace% x)] {a b c a' b' : ℝ} {γ γ' : ℝ → M}

variable (I) in
/-- The length on `Icc a b` of a path into a manifold, where the path is defined on the whole real
line.

We use the whole real line to avoid subtype hell in API, but this is equivalent to
considering functions on the manifold with boundary `Icc a b`, see
`lintegral_norm_mfderiv_Icc_eq_pathELength_projIcc`.

We use `mfderiv` instead of `mfderivWithin` in the definition as these coincide (apart from the two
endpoints which have zero measure) and `mfderiv` is easier to manipulate. However, we give
a lemma `pathELength_eq_integral_mfderivWithin_Icc` to rewrite with the `mfderivWithin` form. -/
irreducible_def pathELength (γ : ℝ → M) (a b : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Icc a b, ‖mfderiv% γ t 1‖ₑ

/-
**Manifold.pathELength_eq_lintegral_mfderiv_Icc** 是 Mathlib 中的一个引理，位于命名空间 `Manif
old`。
形式化陈述：pathELength_eq_lintegral_mfderiv_Icc : pathELength I γ a b = ∫⁻ t in Icc a
 b, ‖mfderiv% γ t 1‖ₑ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Manifold.pathELength_def`：∀ {E : Type u_4} [inst : NormedAddCommGroup E]
 [inst_1 : NormedSpace ℝ E] {H : Type u_5} [inst_2 : TopologicalSpace H]   (I : 
ModelWithCorne…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pathELength_eq_lintegral_mfderiv_Icc :
    pathELength I γ a b = ∫⁻ t in Icc a b, ‖mfderiv% γ t 1‖ₑ := by simp [pathELength]
/-
**Manifold.pathELength_eq_lintegral_mfderiv_Ioo** 是 Mathlib 中的一个引理，位于命名空间 `Manif
old`。
形式化陈述：pathELength_eq_lintegral_mfderiv_Ioo : pathELength I γ a b = ∫⁻ t in Ioo a
 b, ‖mfderiv% γ t 1‖ₑ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Manifold.pathELength_eq_lintegral_mfderiv_Icc`：pathELength_eq_lintegral_
mfderiv_Icc : pathELength I γ a b = ∫⁻ t in Icc a b, ‖mfderiv% γ t 1‖ₑ
· 使用定理 `MeasureTheory.restrict_Ioo_eq_restrict_Icc`：restrict_Ioo_eq_restrict_Icc
 : μ.restrict (Ioo a b) = μ.restrict (Icc a b)
-/
lemma pathELength_eq_lintegral_mfderiv_Ioo :
    pathELength I γ a b = ∫⁻ t in Ioo a b, ‖mfderiv% γ t 1‖ₑ := by
  rw [pathELength_eq_lintegral_mfderiv_Icc, restrict_Ioo_eq_restrict_Icc]
/-
**Manifold.pathELength_eq_lintegral_mfderivWithin_Icc** 是 Mathlib 中的一个引理，位于命名空间 
`Manifold`。
形式化陈述：pathELength_eq_lintegral_mfderivWithin_Icc : pathELength I γ a b = ∫⁻ t in
 Icc a b, ‖mfderiv[Icc a b] γ t 1‖ₑ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Manifold.pathELength_eq_lintegral_mfderiv_Icc`：pathELength_eq_lintegral_
mfderiv_Icc : pathELength I γ a b = ∫⁻ t in Icc a b, ‖mfderiv% γ t 1‖ₑ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.restrict_Ioo_eq_restrict_Icc`：restrict_Ioo_eq_restrict_Icc
 : μ.restrict (Ioo a b) = μ.restrict (Icc a b)
· 使用定理 `MeasureTheory.setLIntegral_congr_fun`：setLIntegral_congr_fun {f g : α ->
 Real>=0∞} {s : Set α} (hs : MeasurableSet s) (hfg : EqOn f g s) : ∫⁻ x in s, f 
x ∂μ = ∫⁻ x in s, g x ∂μ
· 使用定理 `measurableSet_Ioo`：measurableSet_Ioo [OrderClosedTopology α] : Measurabl
eSet (Ioo a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `mfderivWithin_of_mem_nhds`：mfderivWithin_of_mem_nhds (h : s in 𝓝 x) : mf
deriv[s] f x = mfderiv% f x
· 使用定理 `Icc_mem_nhds`：Icc_mem_nhds {a b x : α} (ha : a < x) (hb : x < b) : Icc a
 b in 𝓝 x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma pathELength_eq_lintegral_mfderivWithin_Icc :
    pathELength I γ a b = ∫⁻ t in Icc a b, ‖mfderiv[Icc a b] γ t 1‖ₑ := by
  -- we use that the endpoints have measure 0 to rewrite on `Ioo a b`, where `mfderiv` and
  -- `mfderivWithin` coincide.
  rw [pathELength_eq_lintegral_mfderiv_Icc, ← restrict_Ioo_eq_restrict_Icc]
  apply setLIntegral_congr_fun measurableSet_Ioo (fun t ht ↦ ?_)
  rw [mfderivWithin_of_mem_nhds]
  exact Icc_mem_nhds ht.1 ht.2
/-
**Manifold.pathELength_self** 是 Mathlib 中的一个定理，位于命名空间 `Manifold`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] 
{H : Type u_2} [inst_2 : TopologicalSpace H]   {I : ModelWithCorners ℝ E H} {M :
 Type u_3} [inst_3 : TopologicalSpace M] [inst_4 : ChartedSpace H M]   [inst_5 :
 (x : M) → ENorm (TangentSpace I x)] {a : ℝ} {γ : ℝ → M}, Manifold.pathELength I
 γ a a = 0
参数：x : M；TangentSpace I x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Manifold.pathELength_def`：∀ {E : Type u_4} [inst : NormedAddCommGroup E]
 [inst_1 : NormedSpace ℝ E] {H : Type u_5} [inst_2 : TopologicalSpace H]   (I : 
ModelWithCorne…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Set.Icc_self`：Icc_self (a : α) : Icc a a = {a}
· 使用定理 `MeasureTheory.Measure.restrict_singleton`：restrict_singleton (μ : Measur
e α) (a : α) : μ.restrict {a} = μ {a} • dirac a
· 使用定理 `MeasureTheory.NullSingletonClass.measure_singleton`：∀ {α : Type u_1} {m0
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.NullSi
ngletonClass μ]   (x : α), μ {x} = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `MeasureTheory.lintegral_zero_measure`：lintegral_zero_measure {m : Measur
ableSpace α} (f : α -> Real>=0∞) : ∫⁻ a, f a ∂(0 : Measure α) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma pathELength_self : pathELength I γ a a = 0 := by
  simp [pathELength]
/-
**Manifold.pathELength_congr_Ioo** 是 Mathlib 中的一个引理，位于命名空间 `Manifold`。
形式化陈述：pathELength_congr_Ioo (h : EqOn γ γ' (Ioo a b)) : pathELength I γ a b = pa
thELength I γ' a b
参数：h : EqOn γ γ' (Ioo a b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Manifold.pathELength_eq_lintegral_mfderiv_Ioo`：pathELength_eq_lintegral_
mfderiv_Ioo : pathELength I γ a b = ∫⁻ t in Ioo a b, ‖mfderiv% γ t 1‖ₑ
· 使用定理 `MeasureTheory.setLIntegral_congr_fun`：setLIntegral_congr_fun {f g : α ->
 Real>=0∞} {s : Set α} (hs : MeasurableSet s) (hfg : EqOn f g s) : ∫⁻ x in s, f 
x ∂μ = ∫⁻ x in s, g x ∂μ
· 使用定理 `measurableSet_Ioo`：measurableSet_Ioo [OrderClosedTopology α] : Measurabl
eSet (Ioo a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Filter.EventuallyEq.mfderiv_eq`：Filter.EventuallyEq.mfderiv_eq (hL : f₁ 
=ᶠ[𝓝 x] f) : mfderiv% f₁ x = mfderiv% f x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Ioo_mem_nhds`：Ioo_mem_nhds {a b x : α} (ha : a < x) (hb : x < b) : Ioo a
 b in 𝓝 x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
-/
lemma pathELength_congr_Ioo (h : EqOn γ γ' (Ioo a b)) :
    pathELength I γ a b = pathELength I γ' a b := by
  simp only [pathELength_eq_lintegral_mfderiv_Ioo]
  apply setLIntegral_congr_fun measurableSet_Ioo (fun t ht ↦ ?_)
  have A : γ t = γ' t := h ht
  congr! 2
  apply Filter.EventuallyEq.mfderiv_eq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with a ha using h ha
/-
**Manifold.pathELength_congr** 是 Mathlib 中的一个引理，位于命名空间 `Manifold`。
形式化陈述：pathELength_congr (h : EqOn γ γ' (Icc a b)) : pathELength I γ a b = pathEL
ength I γ' a b
参数：h : EqOn γ γ' (Icc a b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.pathELength_congr_Ioo`：pathELength_congr_Ioo (h : EqOn γ γ' (Io
o a b)) : pathELength I γ a b = pathELength I γ' a b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma pathELength_congr (h : EqOn γ γ' (Icc a b)) : pathELength I γ a b = pathELength I γ' a b :=
  pathELength_congr_Ioo (fun _ hx ↦ h ⟨hx.1.le, hx.2.le⟩)

@[gcongr]
/-
**Manifold.pathELength_mono** 是 Mathlib 中的一个引理，位于命名空间 `Manifold`。
形式化陈述：pathELength_mono (h : a' <= a) (h' : b <= b') : pathELength I γ a b <= pat
hELength I γ a' b'
参数：h : a' <= a；h' : b <= b'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Manifold.pathELength_eq_lintegral_mfderiv_Icc`：pathELength_eq_lintegral_
mfderiv_Icc : pathELength I γ a b = ∫⁻ t in Icc a b, ‖mfderiv% γ t 1‖ₑ
· 使用定理 `MeasureTheory.lintegral_mono_set`：lintegral_mono_set {_ : MeasurableSpac
e α} ⦃μ : Measure α⦄ {s t : Set α} {f : α -> Real>=0∞} (hst : s subseteq t) : ∫⁻
 x in s, f x ∂μ <= ∫⁻ …
· 使用定理 `Set.Icc_subset_Icc`：Icc_subset_Icc (ha : a₂ <= a₁) (hb : b₁ <= b₂) : Icc
 a₁ b₁ subseteq Icc a₂ b₂
-/
lemma pathELength_mono (h : a' ≤ a) (h' : b ≤ b') :
    pathELength I γ a b ≤ pathELength I γ a' b' := by
  simpa [pathELength_eq_lintegral_mfderiv_Icc] using lintegral_mono_set (Icc_subset_Icc h h')
/-
**Manifold.pathELength_add** 是 Mathlib 中的一个引理，位于命名空间 `Manifold`。
形式化陈述：pathELength_add (h : a <= b) (h' : b <= c) : pathELength I γ a b + pathELe
ngth I γ b c = pathELength I γ a c
参数：h : a <= b；h' : b <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Icc_union_Ioc_eq_Icc`：Icc_union_Ioc_eq_Icc (h₁ : a <= b) (h₂ : b <= 
c) : Icc a b union Ioc b c = Icc a c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Manifold.pathELength_def`：∀ {E : Type u_4} [inst : NormedAddCommGroup E]
 [inst_1 : NormedSpace ℝ E] {H : Type u_5} [inst_2 : TopologicalSpace H]   (I : 
ModelWithCorne…
· 使用定理 `MeasureTheory.lintegral_union`：lintegral_union {f : α -> Real>=0∞} {A B 
: Set α} (hB : MeasurableSet B) (hAB : Disjoint A B) : ∫⁻ a in A union B, f a ∂μ
 = ∫⁻ a in A, f a ∂…
· 使用定理 `measurableSet_Ioc`：measurableSet_Ioc [ClosedIicTopology α] : MeasurableS
et (Ioc a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.disjoint_iff_forall_ne`：disjoint_iff_forall_ne : Disjoint s t ↔ fora
ll ⦃a⦄, a in s -> forall ⦃b⦄, b in t -> a != b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.restrict_Ioc_eq_restrict_Icc`：restrict_Ioc_eq_restrict_Icc
 : μ.restrict (Ioc a b) = μ.restrict (Icc a b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pathELength_add (h : a ≤ b) (h' : b ≤ c) :
    pathELength I γ a b + pathELength I γ b c = pathELength I γ a c := by
  symm
  have : Icc a c = Icc a b ∪ Ioc b c := (Icc_union_Ioc_eq_Icc h h').symm
  rw [pathELength, this, lintegral_union measurableSet_Ioc]; swap
  · exact disjoint_iff_forall_ne.mpr (fun a ha b hb ↦ (ha.2.trans_lt hb.1).ne)
  simp [restrict_Ioc_eq_restrict_Icc, pathELength]

attribute [local instance] Measure.Subtype.measureSpace

/-- Given a path `γ` defined on the manifold with boundary `[a, b]`, its length (as the integral of
the norm of its manifold derivative) coincides with `pathELength` of the lift of `γ` to the real
line, between `a` and `b`. -/
/-
**Manifold.lintegral_norm_mfderiv_Icc_eq_pathELength_projIcc** 是 Mathlib 中的一个引理，
位于命名空间 `Manifold`。
形式化陈述：lintegral_norm_mfderiv_Icc_eq_pathELength_projIcc {a b : Real} [h : Fact (
a < b)] {γ : Icc a b -> M} : ∫⁻ t, ‖mfderiv% γ t 1‖ₑ = pathELength I (γ ∘ (projI
cc a b h.out.le)) a b
参数：a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Manifold.pathELength_eq_lintegral_mfderivWithin_Icc`：pathELength_eq_lint
egral_mfderivWithin_Icc : pathELength I γ a b = ∫⁻ t in Icc a b, ‖mfderiv[Icc a 
b] γ t 1‖ₑ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `MeasureTheory.measurePreserving_subtype_coe`：measurePreserving_subtype_c
oe {s : Set α} (hs : MeasurableSet s) : MeasurePreserving (Subtype.val : s -> α)
 (μa.comap Subtype.val) (μa.restr…
· 使用定理 `measurableSet_Icc`：measurableSet_Icc [OrderClosedTopology α] : Measurabl
eSet (Icc a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MeasurePreserving.lintegral_comp_emb`：lintegral_comp_emb (
hge : MeasurableEmbedding g) (f : β -> Real>=0∞) : ∫⁻ a, f (g a) ∂μ = ∫⁻ b, f b 
∂ν
· 使用定理 `MeasurableEmbedding.subtype_coe`：subtype_coe (hs : MeasurableSet s) : Me
asurableEmbedding ((↑) : s -> α) where injective
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.projIcc_val`：projIcc_val (x : Icc a b) : projIcc a b h x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'

--- 原说明 ---
Given a path `γ` defined on the manifold with boundary `[a, b]`, its length (as 
the integral of
the norm of its manifold derivative) coincides with `pathELength` of the lift of
 `γ` to the real
line, between `a` and `b`.
-/
lemma lintegral_norm_mfderiv_Icc_eq_pathELength_projIcc {a b : ℝ}
    [h : Fact (a < b)] {γ : Icc a b → M} :
    ∫⁻ t, ‖mfderiv% γ t 1‖ₑ = pathELength I (γ ∘ (projIcc a b h.out.le)) a b := by
  rw [pathELength_eq_lintegral_mfderivWithin_Icc]
  simp_rw [← mfderivWithin_comp_projIcc_one]
  have : MeasurePreserving (Subtype.val : Icc a b → ℝ) volume
    (volume.restrict (Icc a b)) := measurePreserving_subtype_coe measurableSet_Icc
  rw [← MeasurePreserving.lintegral_comp_emb this
    (MeasurableEmbedding.subtype_coe measurableSet_Icc)]
  congr
  ext t
  have : t = projIcc a b h.out.le (t : ℝ) := by simp
  congr

open MeasureTheory

variable [∀ (x : M), ENormSMulClass ℝ (TangentSpace% x)]

set_option backward.isDefEq.respectTransparency false in
/-- The length of a path in a manifold is invariant under a monotone reparametrization. -/
/-
**Manifold.pathELength_comp_of_monotoneOn** 是 Mathlib 中的一个引理，位于命名空间 `Manifold`。
形式化陈述：pathELength_comp_of_monotoneOn {f : Real -> Real} (h : a <= b) (hf : Monot
oneOn f (Icc a b)) (h'f : DifferentiableOn Real f (Icc a b)) (hγ : MDiff[Icc (f 
a) (f b)] γ) : pathELength I (γ ∘ f) a b = pathELength I γ (f a) (f b)
参数：h : a <= b；hf : MonotoneOn f (Icc a b)；h'f : DifferentiableOn Real f (Icc a b
)；hγ : MDiff[Icc (f a) (f b)] γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Manifold.pathELength_self`：∀ {E : Type u_1} [inst : NormedAddCommGroup E
] [inst_1 : NormedSpace ℝ E] {H : Type u_2} [inst_2 : TopologicalSpace H]   {I :
 ModelWithCorne…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ContinuousOn.image_Icc_of_monotoneOn`：ContinuousOn.image_Icc_of_monotone
On (hab : a <= b) (hf : ContinuousOn f (Icc a b)) (hmono : MonotoneOn f (Icc a b
)) : f '' Icc a b = Icc (f…
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
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `DifferentiableOn.continuousOn`：DifferentiableOn.continuousOn (h : Differ
entiableOn 𝕜 f s) : ContinuousOn f s
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用引理 `Manifold.pathELength_eq_lintegral_mfderivWithin_Icc`：pathELength_eq_lint
egral_mfderivWithin_Icc : pathELength I γ a b = ∫⁻ t in Icc a b, ‖mfderiv[Icc a 
b] γ t 1‖ₑ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x
· 使用定理 `MeasureTheory.lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn`：lint
egral_image_eq_lintegral_deriv_mul_of_monotoneOn (hs : MeasurableSet s) (hf' : f
orall x in s, HasDerivWithinAt f (f' x) s x) (hf : Monot…
（共 47 条，此处仅展示前 30 条）

--- 原说明 ---
The length of a path in a manifold is invariant under a monotone reparametrizati
on.
-/
lemma pathELength_comp_of_monotoneOn {f : ℝ → ℝ} (h : a ≤ b) (hf : MonotoneOn f (Icc a b))
    (h'f : DifferentiableOn ℝ f (Icc a b)) (hγ : MDiff[Icc (f a) (f b)] γ) :
    pathELength I (γ ∘ f) a b = pathELength I γ (f a) (f b) := by
  rcases h.eq_or_lt with rfl | h
  · simp
  have f_im : f '' (Icc a b) = Icc (f a) (f b) := h'f.continuousOn.image_Icc_of_monotoneOn h.le hf
  simp only [pathELength_eq_lintegral_mfderivWithin_Icc, ← f_im]
  have B (t) (ht : t ∈ Icc a b) : HasDerivWithinAt f (derivWithin f (Icc a b) t) (Icc a b) t :=
    (h'f t ht).hasDerivWithinAt
  rw [lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn measurableSet_Icc B hf]
  apply setLIntegral_congr_fun measurableSet_Icc (fun t ht ↦ ?_)
  have : (mfderiv[Icc a b] (γ ∘ f) t) =
      (mfderiv[Icc (f a) (f b)] γ (f t)) ∘L mfderiv[Icc a b] f t := by
    rw [← f_im] at hγ ⊢
    apply mfderivWithin_comp
    · apply hγ _ (mem_image_of_mem _ ht)
    · rw [mdifferentiableWithinAt_iff_differentiableWithinAt]
      exact h'f _ ht
    · exact subset_preimage_image _ _
    · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
      exact uniqueDiffOn_Icc h _ ht
  rw [this]
  simp only [Function.comp_apply, ContinuousLinearMap.comp_apply]
  have : mfderiv[Icc a b] f t 1 = derivWithin f (Icc a b) t • (1 : TangentSpace% (f t)) := by
    simp only [mfderivWithin_eq_fderivWithin, ← fderivWithin_derivWithin, smul_eq_mul, mul_one]
    rfl
  rw [this]
  have : 0 ≤ derivWithin f (Icc a b) t := hf.derivWithin_nonneg
  simp only [map_smul, enorm_smul, ← Real.enorm_of_nonneg this, f_im]

set_option backward.isDefEq.respectTransparency false in
/-- The length of a path in a manifold is invariant under an antitone reparametrization. -/
/-
**Manifold.pathELength_comp_of_antitoneOn** 是 Mathlib 中的一个引理，位于命名空间 `Manifold`。
形式化陈述：pathELength_comp_of_antitoneOn {f : Real -> Real} (h : a <= b) (hf : Antit
oneOn f (Icc a b)) (h'f : DifferentiableOn Real f (Icc a b)) (hγ : MDiff[Icc (f 
b) (f a)] γ) : pathELength I (γ ∘ f) a b = pathELength I γ (f b) (f a)
参数：h : a <= b；hf : AntitoneOn f (Icc a b)；h'f : DifferentiableOn Real f (Icc a b
)；hγ : MDiff[Icc (f b) (f a)] γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Manifold.pathELength_self`：∀ {E : Type u_1} [inst : NormedAddCommGroup E
] [inst_1 : NormedSpace ℝ E] {H : Type u_2} [inst_2 : TopologicalSpace H]   {I :
 ModelWithCorne…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ContinuousOn.image_Icc_of_antitoneOn`：ContinuousOn.image_Icc_of_antitone
On (hab : a <= b) (hf : ContinuousOn f (Icc a b)) (hmono : AntitoneOn f (Icc a b
)) : f '' Icc a b = Icc (f…
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
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `DifferentiableOn.continuousOn`：DifferentiableOn.continuousOn (h : Differ
entiableOn 𝕜 f s) : ContinuousOn f s
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用引理 `Manifold.pathELength_eq_lintegral_mfderivWithin_Icc`：pathELength_eq_lint
egral_mfderivWithin_Icc : pathELength I γ a b = ∫⁻ t in Icc a b, ‖mfderiv[Icc a 
b] γ t 1‖ₑ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x
· 使用定理 `MeasureTheory.lintegral_image_eq_lintegral_deriv_mul_of_antitoneOn`：lint
egral_image_eq_lintegral_deriv_mul_of_antitoneOn (hs : MeasurableSet s) (hf' : f
orall x in s, HasDerivWithinAt f (f' x) s x) (hf : Antit…
（共 50 条，此处仅展示前 30 条）

--- 原说明 ---
The length of a path in a manifold is invariant under an antitone reparametrizat
ion.
-/
lemma pathELength_comp_of_antitoneOn {f : ℝ → ℝ} (h : a ≤ b) (hf : AntitoneOn f (Icc a b))
    (h'f : DifferentiableOn ℝ f (Icc a b)) (hγ : MDiff[Icc (f b) (f a)] γ) :
    pathELength I (γ ∘ f) a b = pathELength I γ (f b) (f a) := by
  rcases h.eq_or_lt with rfl | h
  · simp
  have f_im : f '' (Icc a b) = Icc (f b) (f a) := h'f.continuousOn.image_Icc_of_antitoneOn h.le hf
  simp only [pathELength_eq_lintegral_mfderivWithin_Icc, ← f_im]
  have B (t) (ht : t ∈ Icc a b) : HasDerivWithinAt f (derivWithin f (Icc a b) t) (Icc a b) t :=
    (h'f t ht).hasDerivWithinAt
  rw [lintegral_image_eq_lintegral_deriv_mul_of_antitoneOn measurableSet_Icc B hf]
  apply setLIntegral_congr_fun measurableSet_Icc (fun t ht ↦ ?_)
  have : (mfderiv[Icc a b] (γ ∘ f) t)
      = (mfderiv[Icc (f b) (f a)] γ (f t)) ∘L mfderiv[Icc a b] f t := by
    rw [← f_im] at hγ ⊢
    apply mfderivWithin_comp
    · apply hγ _ (mem_image_of_mem _ ht)
    · rw [mdifferentiableWithinAt_iff_differentiableWithinAt]
      exact h'f _ ht
    · exact subset_preimage_image _ _
    · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
      exact uniqueDiffOn_Icc h _ ht
  rw [this]
  simp only [Function.comp_apply, ContinuousLinearMap.comp_apply]
  have : mfderiv[Icc a b] f t 1
      = derivWithin f (Icc a b) t • (1 : TangentSpace% (f t)) := by
    simp only [mfderivWithin_eq_fderivWithin, ← fderivWithin_derivWithin, smul_eq_mul, mul_one]
    rfl
  rw [this]
  have : 0 ≤ -derivWithin f (Icc a b) t := by simp [hf.derivWithin_nonpos]
  simp only [map_smul, enorm_smul, f_im, ← Real.enorm_of_nonneg this, enorm_neg]

section

variable {x y z : M} {r : ℝ≥0∞} {a b : ℝ}

variable (I) in
/-- The Riemannian extended distance between two points, in a manifold where the tangent spaces
have an extended norm, defined as the infimum of the lengths of `C^1` paths between the points. -/
noncomputable irreducible_def riemannianEDist (x y : M) : ℝ≥0∞ :=
  ⨅ (γ : Path x y) (_ : CMDiff 1 γ), ∫⁻ x, ‖mfderiv% γ x 1‖ₑ

/-- The Riemannian edistance is bounded above by the length of any `C^1` path from `x` to `y`.
Here, we express this using a path defined on the whole real line, considered on
some interval `[a, b]`. -/
/-
**Manifold.riemannianEDist_le_pathELength** 是 Mathlib 中的一个引理，位于命名空间 `Manifold`。
形式化陈述：riemannianEDist_le_pathELength {γ : Real -> M} (hγ : CMDiff[Icc a b] 1 γ) 
(ha : γ a = x) (hb : γ b = y) (hab : a <= b) : riemannianEDist I x y <= pathELen
gth I γ a b
参数：hγ : CMDiff[Icc a b] 1 γ；ha : γ a = x；hb : γ b = y；hab : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsTopologicalAddTorsor.toContinuousVAdd`：∀ {V : Type u_1} {inst : AddGro
up V} {inst_1 : TopologicalSpace V} {P : Type u_2} {inst_2 : AddTorsor V P}   {i
nst_3 : TopologicalSpace P} […
· 使用定理 `instIsTopologicalAddTorsor_1`：∀ {V : Type u_2} {P : Type u_3} [inst : Se
minormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTors
or V P], IsTopolog…
· 使用定理 `ContMDiffOn.comp`：ContMDiffOn.comp {t : Set M'} {g : M' -> M''} (hg : Co
ntMDiffOn I' I'' n g t) (hf : ContMDiffOn I I' n f s) (st : s subseteq f ⁻¹' t) 
: Cont…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `contMDiffOn_iff_contDiffOn`：contMDiffOn_iff_contDiffOn {f : E -> E'} {s 
: Set E} : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E') n f s ↔ ContDiffOn 𝕜 n f s
· 使用定理 `ContDiff.contDiffOn`：ContDiff.contDiffOn (h : ContDiff 𝕜 n f) : ContDiff
On 𝕜 n f s
· 使用定理 `ContinuousAffineMap.contDiff`：contDiff {n : WithTop Nat∞} (f : V ->ᴬ[𝕜] 
W) : ContDiff 𝕜 n f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用引理 `ContinuousAffineMap.coe_lineMap_eq`：coe_lineMap_eq (p₀ p₁ : P) [Topologi
calSpace R] [TopologicalSpace V] [ContinuousSMul R V] [ContinuousVAdd V P] : ⇑(C
ontinuousAffineMap.lineM…
· 使用定理 `segment_eq_image_lineMap`：segment_eq_image_lineMap (x y : E) : [x -[𝕜] y
] = AffineMap.lineMap x y '' Icc (0 : 𝕜) 1
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `segment_eq_Icc`：segment_eq_Icc (h : x <= y) : [x -[𝕜] y] = Icc x y
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用引理 `contMDiffOn_comp_projIcc_iff`：contMDiffOn_comp_projIcc_iff {f : Icc x y 
-> M} : CMDiff[Icc x y] n (f ∘ (Set.projIcc x y h.out.le)) ↔ CMDiff n f
· 使用定理 `ContMDiffOn.congr`：ContMDiffOn.congr (h : ContMDiffOn I I' n f s) (h₁ : 
forall y in s, f₁ y = f y) : ContMDiffOn I I' n f₁ s
· 使用定理 `Set.projIcc_of_mem`：projIcc_of_mem (hx : x in Icc a b) : projIcc a b h x
 = ⟨x, hx⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ContMDiff.continuous`：ContMDiff.continuous (hf : ContMDiff I I' n f) : C
ontinuous f
· 使用定理 `AffineMap.lineMap_apply_zero`：lineMap_apply_zero (p₀ p₁ : P1) : lineMap 
p₀ p₁ (0 : k) = p₀
（共 48 条，此处仅展示前 30 条）

--- 原说明 ---
The Riemannian edistance is bounded above by the length of any `C^1` path from `
x` to `y`.
Here, we express this using a path defined on the whole real line, considered on
some interval `[a, b]`.
-/
lemma riemannianEDist_le_pathELength {γ : ℝ → M} (hγ : CMDiff[Icc a b] 1 γ)
    (ha : γ a = x) (hb : γ b = y) (hab : a ≤ b) :
    riemannianEDist I x y ≤ pathELength I γ a b := by
  let η : ℝ →ᴬ[ℝ] ℝ := ContinuousAffineMap.lineMap a b
  have hη : CMDiff[Icc 0 1] 1 (γ ∘ η) := by
    apply hγ.comp
    · rw [contMDiffOn_iff_contDiffOn]
      exact η.contDiff.contDiffOn
    · rw [← image_subset_iff, ContinuousAffineMap.coe_lineMap_eq, ← segment_eq_image_lineMap]
      simp [hab]
  let f : unitInterval → M := fun t ↦ (γ ∘ η) t
  have hf : CMDiff 1 f := by
    rw [← contMDiffOn_comp_projIcc_iff]
    apply hη.congr (fun t ht ↦ ?_)
    simp only [Function.comp_apply, f, projIcc_of_mem, ht]
  let g : Path x y := by
    refine ⟨⟨f, hf.continuous⟩, ?_, ?_⟩ <;>
    simp [f, η, ContinuousAffineMap.coe_lineMap_eq, ha, hb]
  have A : riemannianEDist I x y ≤ ∫⁻ x, ‖mfderiv% g x 1‖ₑ := by
    rw [riemannianEDist]; exact biInf_le _ hf
  apply A.trans_eq
  rw [lintegral_norm_mfderiv_Icc_eq_pathELength_projIcc]
  have E : pathELength I (g ∘ projIcc 0 1 zero_le_one) 0 1 = pathELength I (γ ∘ η) 0 1 := by
    apply pathELength_congr (fun t ht ↦ ?_)
    simp only [Function.comp_apply, ht, projIcc_of_mem]
    rfl
  rw [E, pathELength_comp_of_monotoneOn zero_le_one _ η.differentiableOn]
  · simp [η, ContinuousAffineMap.coe_lineMap_eq]
  · simpa [η, ContinuousAffineMap.coe_lineMap_eq] using hγ.mdifferentiableOn one_ne_zero
  · apply (AffineMap.lineMap_mono hab).monotoneOn

omit [∀ (x : M), ENormSMulClass ℝ (TangentSpace% x)] in
/-- If some `r` is strictly larger than the Riemannian edistance between two points, there exists
a path between these two points of length `< r`. Here, we get such a path on `[0, 1]`.
For a more precise version giving locally constant paths around the endpoints, see
`exists_lt_locally_constant_of_riemannianEDist_lt` -/
/-
**Manifold.exists_lt_of_riemannianEDist_lt** 是 Mathlib 中的一个引理，位于命名空间 `Manifold`。
形式化陈述：exists_lt_of_riemannianEDist_lt (hr : riemannianEDist I x y < r) : exists 
γ : Real -> M, γ 0 = x ∧ γ 1 = y ∧ CMDiff[Icc 0 1] 1 γ ∧ pathELength I γ 0 1 < r
参数：hr : riemannianEDist I x y < r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Manifold.riemannianEDist_def`：∀ {E : Type u_4} [inst : NormedAddCommGrou
p E] [inst_1 : NormedSpace ℝ E] {H : Type u_5} [inst_2 : TopologicalSpace H]   (
I : ModelWithCorne…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.projIcc_left`：projIcc_left : projIcc a b h a = ⟨a, left_mem_Icc.2 h⟩
· 使用定理 `Path.source`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} (γ :
 Path x y), γ 0 = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.projIcc_right`：projIcc_right : projIcc a b h b = ⟨b, right_mem_Icc.2
 h⟩
· 使用定理 `Path.target`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} (γ :
 Path x y), γ 1 = y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `contMDiffOn_comp_projIcc_iff`：contMDiffOn_comp_projIcc_iff {f : Icc x y 
-> M} : CMDiff[Icc x y] n (f ∘ (Set.projIcc x y h.out.le)) ↔ CMDiff n f
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Manifold.lintegral_norm_mfderiv_Icc_eq_pathELength_projIcc`：lintegral_no
rm_mfderiv_Icc_eq_pathELength_projIcc {a b : Real} [h : Fact (a < b)] {γ : Icc a
 b -> M} : ∫⁻ t, ‖mfderiv% γ t 1‖ₑ = pathELength…

--- 原说明 ---
If some `r` is strictly larger than the Riemannian edistance between two points,
 there exists
a path between these two points of length `< r`. Here, we get such a path on `[0
, 1]`.
For a more precise version giving locally constant paths around the endpoints, s
ee
`exists_lt_locally_constant_of_riemannianEDist_lt`
-/
lemma exists_lt_of_riemannianEDist_lt (hr : riemannianEDist I x y < r) :
    ∃ γ : ℝ → M, γ 0 = x ∧ γ 1 = y ∧ CMDiff[Icc 0 1] 1 γ ∧
    pathELength I γ 0 1 < r := by
  simp only [riemannianEDist, iInf_lt_iff, exists_prop] at hr
  rcases hr with ⟨γ, γ_smooth, hγ⟩
  refine ⟨γ ∘ (projIcc 0 1 zero_le_one), by simp, by simp,
    contMDiffOn_comp_projIcc_iff.2 γ_smooth, ?_⟩
  rwa [← lintegral_norm_mfderiv_Icc_eq_pathELength_projIcc]

/-- If some `r` is strictly larger than the Riemannian edistance between two points, there exists
a path between these two points of length `< r`. Here, we get such a path on an arbitrary interval
`[a, b]` with `a < b`, and moreover we ensure that the path is locally constant around `a` and `b`,
which is convenient for gluing purposes. -/
/-
**Manifold.exists_lt_locally_constant_of_riemannianEDist_lt** 是 Mathlib 中的一个引理，位
于命名空间 `Manifold`。
形式化陈述：exists_lt_locally_constant_of_riemannianEDist_lt (hr : riemannianEDist I x
 y < r) (hab : a < b) : exists γ : Real -> M, γ a = x ∧ γ b = y ∧ CMDiff 1 γ ∧ p
athELength I γ a b < r ∧ γ =ᶠ[𝓝 a] (fun _ => x) ∧ γ =ᶠ[𝓝 b] (fun _ => y)
参数：hr : riemannianEDist I x y < r；hab : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.exists_lt_of_riemannianEDist_lt`：exists_lt_of_riemannianEDist_l
t (hr : riemannianEDist I x y < r) : exists γ : Real -> M, γ 0 = x ∧ γ 1 = y ∧ C
MDiff[Icc 0 1] 1 γ ∧ pathELeng…
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
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
· 使用定理 `mul_nonpos_of_nonneg_of_nonpos`：mul_nonpos_of_nonneg_of_nonpos [PosMulMo
no α] (ha : 0 <= a) (hb : b <= 0) : a * b <= 0
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
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
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
（共 94 条，此处仅展示前 30 条）

--- 原说明 ---
If some `r` is strictly larger than the Riemannian edistance between two points,
 there exists
a path between these two points of length `< r`. Here, we get such a path on an 
arbitrary interval
`[a, b]` with `a < b`, and moreover we ensure that the path is locally constant 
around `a` and `b`,
which is convenient for gluing purposes.
-/
lemma exists_lt_locally_constant_of_riemannianEDist_lt
    (hr : riemannianEDist I x y < r) (hab : a < b) :
    ∃ γ : ℝ → M, γ a = x ∧ γ b = y ∧ CMDiff 1 γ ∧
    pathELength I γ a b < r ∧ γ =ᶠ[𝓝 a] (fun _ ↦ x) ∧ γ =ᶠ[𝓝 b] (fun _ ↦ y) := by
  /- We start from a path from `x` to `y` defined on `[0, 1]` with length `< r`. Then, we
  reparameterize it using a smooth monotone map `η` from `[a, b]` to `[0, 1]` which is moreover
  locally constant around `a` and `b`.
  Such a map is easy to build with `Real.smoothTransition`.

  Note that this is a very standard construction in differential topology.
  TODO: refactor once we have more differential topology in Mathlib and this gets duplicated. -/
  rcases exists_lt_of_riemannianEDist_lt hr with ⟨γ, hγx, hγy, γ_smooth, hγ⟩
  rcases exists_between hab with ⟨a', haa', ha'b⟩
  rcases exists_between ha'b with ⟨b', ha'b', hb'b⟩
  let η (t : ℝ) : ℝ := Real.smoothTransition ((b' - a')⁻¹ * (t - a'))
  have A (t) (ht : t < a') : η t = 0 := by
    simp only [η, Real.smoothTransition.zero_iff_nonpos]
    apply mul_nonpos_of_nonneg_of_nonpos
    · simpa using ha'b'.le
    · linarith
  have A' (t) (ht : t < a') : (γ ∘ η) t = x := by simp [A t ht, hγx]
  have B (t) (ht : b' < t) : η t = 1 := by
    simp only [η, Real.smoothTransition.eq_one_iff_one_le, inv_mul_eq_div]
    rw [one_le_div₀] <;> linarith
  have B' (t) (ht : b' < t) : (γ ∘ η) t = y := by simp [B t ht, hγy]
  refine ⟨γ ∘ η, A' _ haa', B' _ hb'b, ?_, ?_, ?_, ?_⟩
  · rw [← contMDiffOn_univ]
    apply γ_smooth.comp
    · rw [contMDiffOn_univ, contMDiff_iff_contDiff]
      fun_prop
    · intro t ht
      exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  · convert! hγ using 1
    rw [← A a haa', ← B b hb'b]
    apply pathELength_comp_of_monotoneOn hab.le
    · apply Monotone.monotoneOn
      apply Real.smoothTransition.monotone.comp
      intro t u htu
      dsimp only
      gcongr
    · simp only [η]
      apply (ContDiff.contDiffOn _).differentiableOn one_ne_zero
      fun_prop
    · rw [A a haa', B b hb'b]
      apply γ_smooth.mdifferentiableOn one_ne_zero
  · filter_upwards [Iio_mem_nhds haa'] with t ht using A' t ht
  · filter_upwards [Ioi_mem_nhds hb'b] with t ht using B' t ht
/-
**Manifold.riemannianEDist_self** 是 Mathlib 中的一个引理，位于命名空间 `Manifold`。
形式化陈述：riemannianEDist_self : riemannianEDist I x x = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用引理 `Manifold.riemannianEDist_le_pathELength`：riemannianEDist_le_pathELength 
{γ : Real -> M} (hγ : CMDiff[Icc a b] 1 γ) (ha : γ a = x) (hb : γ b = y) (hab : 
a <= b) : riemannianEDist I x…
· 使用定理 `contMDiffOn_const`：contMDiffOn_const : ContMDiffOn I I' n (fun _ : M => 
c) s
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Manifold.pathELength_self`：∀ {E : Type u_1} [inst : NormedAddCommGroup E
] [inst_1 : NormedSpace ℝ E] {H : Type u_2} [inst_2 : TopologicalSpace H]   {I :
 ModelWithCorne…
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
lemma riemannianEDist_self : riemannianEDist I x x = 0 := by
  apply le_antisymm _ bot_le
  exact (riemannianEDist_le_pathELength (γ := fun (t : ℝ) ↦ x) (a := 0) (b := 0)
    contMDiffOn_const rfl rfl le_rfl).trans_eq (by simp)
/-
**Manifold.riemannianEDist_comm** 是 Mathlib 中的一个引理，位于命名空间 `Manifold`。
形式化陈述：riemannianEDist_comm : riemannianEDist I x y = riemannianEDist I y x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_forall_gt`：∀ {α : Type u_2} [inst : LinearOrder α] {a b : α}, (∀ (
c : α), a < c → b < c) → b ≤ a
· 使用引理 `Manifold.exists_lt_locally_constant_of_riemannianEDist_lt`：exists_lt_loc
ally_constant_of_riemannianEDist_lt (hr : riemannianEDist I x y < r) (hab : a < 
b) : exists γ : Real -> M, γ a = x ∧ γ b = y ∧ …
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `ContMDiff.comp`：ContMDiff.comp {g : M' -> M''} (hg : ContMDiff I' I'' n 
g) (hf : ContMDiff I I' n f) : ContMDiff I I'' n (g ∘ f)
· 使用定理 `ContDiff.neg`：ContDiff.neg {f : E -> F} (hf : ContDiff 𝕜 n f) : ContDiff
 𝕜 n fun x => -f x
· 使用定理 `contDiff_id`：contDiff_id : ContDiff 𝕜 n (id : E -> E)
· 使用引理 `Manifold.riemannianEDist_le_pathELength`：riemannianEDist_le_pathELength 
{γ : Real -> M} (hγ : CMDiff[Icc a b] 1 γ) (ha : γ a = x) (hb : γ b = y) (hab : 
a <= b) : riemannianEDist I x…
· 使用定理 `ContMDiff.contMDiffOn`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
H : Type u_…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Manifold.pathELength_comp_of_antitoneOn`：pathELength_comp_of_antitoneOn 
{f : Real -> Real} (h : a <= b) (hf : AntitoneOn f (Icc a b)) (h'f : Differentia
bleOn Real f (Icc a b)) (hγ :…
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `Antitone.antitoneOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Antitone f → ∀ (s : Set α), AntitoneOn f s
· 使用定理 `Monotone.neg`：∀ {α : Type u} {β : Type u_1} [inst : AddGroup α] [inst_1 
: Preorder α] [AddLeftMono α] [AddRightMono α]   [inst_4 : Preorder β] {f : β → 
α}…
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `monotone_id`：monotone_id [Preorder α] : Monotone (id : α -> α)
· 使用定理 `differentiableOn_neg`：differentiableOn_neg : DifferentiableOn 𝕜 (Neg.neg
 : 𝕜 -> 𝕜) s
· 使用定理 `ContMDiffOn.mdifferentiableOn`：ContMDiffOn.mdifferentiableOn (hf : CMDif
f[s] n f) (hn : n != 0) : MDiff[s] f
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
（共 32 条，此处仅展示前 30 条）
-/
lemma riemannianEDist_comm : riemannianEDist I x y = riemannianEDist I y x := by
  suffices H : ∀ x y, riemannianEDist I y x ≤ riemannianEDist I x y from le_antisymm (H y x) (H x y)
  intro x y
  apply le_of_forall_gt (fun r hr ↦ ?_)
  rcases exists_lt_locally_constant_of_riemannianEDist_lt hr zero_lt_one
    with ⟨γ, γ0, γ1, γ_smooth, hγ, -⟩
  let η : ℝ → ℝ := fun t ↦ -t
  have h_smooth : CMDiff 1 (γ ∘ η) := by
    apply γ_smooth.comp ?_
    simp only [contMDiff_iff_contDiff]
    fun_prop
  have : riemannianEDist I y x ≤ pathELength I (γ ∘ η) (η 1) (η 0) := by
    apply riemannianEDist_le_pathELength h_smooth.contMDiffOn <;> simp [η, γ0, γ1]
  rw [← pathELength_comp_of_antitoneOn zero_le_one] at this; rotate_left
  · exact monotone_id.neg.antitoneOn _
  · exact differentiableOn_neg _
  · exact h_smooth.contMDiffOn.mdifferentiableOn one_ne_zero
  apply this.trans_lt
  convert! hγ
  ext t
  simp [η]
/-
**Manifold.riemannianEDist_triangle** 是 Mathlib 中的一个引理，位于命名空间 `Manifold`。
形式化陈述：riemannianEDist_triangle : riemannianEDist I x z <= riemannianEDist I x y 
+ riemannianEDist I y z
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_forall_gt`：∀ {α : Type u_2} [inst : LinearOrder α] {a b : α}, (∀ (
c : α), a < c → b < c) → b ≤ a
· 使用引理 `ENNReal.exists_add_lt_of_add_lt`：exists_add_lt_of_add_lt {x y z : Real>=
0∞} (h : y + z < x) : exists y' > y, exists z' > z, y' + z' < x
· 使用引理 `Manifold.exists_lt_locally_constant_of_riemannianEDist_lt`：exists_lt_loc
ally_constant_of_riemannianEDist_lt (hr : riemannianEDist I x y < r) (hab : a < 
b) : exists γ : Real -> M, γ a = x ∧ γ b = y ∧ …
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `one_lt_two`：one_lt_two [AddLeftStrictMono α] : (1 : α) < 2
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `Manifold.riemannianEDist_le_pathELength`：riemannianEDist_le_pathELength 
{γ : Real -> M} (hγ : CMDiff[Icc a b] 1 γ) (ha : γ a = x) (hb : γ b = y) (hab : 
a <= b) : riemannianEDist I x…
· 使用定理 `ContMDiff.contMDiffOn`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
H : Type u_…
· 使用引理 `ContMDiff.piecewise_Iic`：ContMDiff.piecewise_Iic {E : Type*} [NormedAddC
ommGroup E] [NormedSpace Real E] {H : Type*} [TopologicalSpace H] {I : ModelWith
Corners Real …
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.piecewise_eq_of_mem`：piecewise_eq_of_mem {i : α} (hi : i in s) : s.p
iecewise f g i = f i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.piecewise_eq_of_notMem`：piecewise_eq_of_notMem {i : α} (hi : i ∉ s) 
: s.piecewise f g i = g i
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `zero_le_two`：zero_le_two [Preorder α] [ZeroLEOneClass α] [AddLeftMono α]
 : (0 : α) <= 2
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Manifold.pathELength_add`：pathELength_add (h : a <= b) (h' : b <= c) : p
athELength I γ a b + pathELength I γ b c = pathELength I γ a c
（共 39 条，此处仅展示前 30 条）
-/
lemma riemannianEDist_triangle :
    riemannianEDist I x z ≤ riemannianEDist I x y + riemannianEDist I y z := by
  apply le_of_forall_gt (fun r hr ↦ ?_)
  rcases ENNReal.exists_add_lt_of_add_lt hr with ⟨u, hu, v, hv, huv⟩
  rcases exists_lt_locally_constant_of_riemannianEDist_lt hu zero_lt_one with
    ⟨γ₁, hγ₁0, hγ₁1, hγ₁_smooth, hγ₁, -, hγ₁_const⟩
  rcases exists_lt_locally_constant_of_riemannianEDist_lt hv one_lt_two with
    ⟨γ₂, hγ₂1, hγ₂2, hγ₂_smooth, hγ₂, hγ₂_const, -⟩
  let γ := piecewise (Iic 1) γ₁ γ₂
  have : riemannianEDist I x z ≤ pathELength I γ 0 2 := by
    apply riemannianEDist_le_pathELength
    · apply ContMDiff.contMDiffOn
      exact ContMDiff.piecewise_Iic hγ₁_smooth hγ₂_smooth (hγ₁_const.trans hγ₂_const.symm)
    · simp [γ, hγ₁0]
    · simp [γ, hγ₂2]
    · exact zero_le_two
  apply this.trans_lt (lt_trans ?_ huv)
  rw [← pathELength_add zero_le_one one_le_two]
  gcongr
  · convert! hγ₁ using 1
    apply pathELength_congr
    intro t ht
    simp [γ, ht.2]
  · convert! hγ₂ using 1
    apply pathELength_congr_Ioo
    intro t ht
    simp [γ, ht.1]

end

end Manifold

