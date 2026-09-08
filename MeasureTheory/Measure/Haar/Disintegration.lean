/-
Copyright (c) 2023 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Pushing a Haar measure by a linear map

We show that the push-forward of an additive Haar measure in a vector space under a surjective
linear map is proportional to the Haar measure on the target space,
in `LinearMap.exists_map_addHaar_eq_smul_addHaar`.

We deduce disintegration properties of the Haar measure: to check that a property is true ae,
it suffices to check that it is true ae along all translates of a given vector subspace.
See `MeasureTheory.ae_mem_of_ae_add_linearMap_mem`.

TODO: this holds more generally in any locally compact group, see
[Fremlin, *Measure Theory* (volume 4, 443Q)][fremlin_vol4]
-/

public section

open MeasureTheory Measure Set

open scoped ENNReal

variable {𝕜 E F : Type*}
  [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [MeasurableSpace F] [BorelSpace F] [NormedSpace 𝕜 F] {L : E →ₗ[𝕜] F}
  {μ : Measure E} {ν : Measure F}
  [IsAddHaarMeasure μ] [IsAddHaarMeasure ν]

variable [LocallyCompactSpace E]
variable (L μ ν)

/-- The image of an additive Haar measure under a surjective linear map is proportional to a given
additive Haar measure. The proportionality factor will be infinite if the linear map has a
nontrivial kernel. -/
/-
**LinearMap.exists_map_addHaar_eq_smul_addHaar'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.exists_map_addHaar_eq_smul_addHaar' (h : Function.Surjective L) 
: exists (c : Real>=0∞), 0 < c ∧ c < ∞ ∧ μ.map L = (c * addHaar (univ : Set (Lin
earMap.ker L))) • ν
参数：h : Function.Surjective L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteDimensional.of_locallyCompactSpace`：FiniteDimensional.of_locallyCo
mpactSpace [WeaklyLocallyCompactSpace E] : FiniteDimensional 𝕜 E
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `Function.Surjective.subsingleton`：∀ {α : Sort u_1} {β : Sort u_2} {f : α
 → β} [Subsingleton α], Function.Surjective f → Subsingleton β
· 使用定理 `proper_of_compact`：∀ {α : Type u} [inst : PseudoMetricSpace α] [CompactS
pace α], ProperSpace α
· 使用定理 `TopologicalSpace.NoetherianSpace.compactSpace`：∀ (α : Type u_1) [inst : 
TopologicalSpace α] [h : TopologicalSpace.NoetherianSpace α], CompactSpace α
· 使用定理 `TopologicalSpace.instNoetherianSpaceOfIndiscreteTopology`：∀ {α : Type u_
1} [inst : TopologicalSpace α] [IndiscreteTopology α], TopologicalSpace.Noetheri
anSpace α
· 使用定理 `instIndiscreteTopologyOfSubsingleton`：∀ {α : Type u} [inst : Topological
Space α] [Subsingleton α], IndiscreteTopology α
· 使用引理 `ProperSpace.of_locallyCompact_module`：ProperSpace.of_locallyCompact_modu
le (V : Type*) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [
T2Space V] [Nontrivial V] …
· 使用定理 `Module.Finite.of_surjective`：of_surjective [hM : Module.Finite R M] (f :
 M ->ₛₗ[σ] P) (hf : Surjective f) : Module.Finite S P
· 使用定理 `FiniteDimensional.proper`：FiniteDimensional.proper [FiniteDimensional 𝕜 
E] : ProperSpace E
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `instProperSpaceSubtypeMemSubmoduleOfCompleteSpaceOfLocallyCompactSpace`：
∀ {𝕜 : Type u_1} {E : Type u_2} [inst : NontriviallyNormedField 𝕜] [CompleteSpac
e 𝕜] [inst_2 : NormedAddCommGroup E]   [inst_3 : NormedSpace…
· 使用定理 `Submodule.exists_isCompl`：Submodule.exists_isCompl (p : Submodule K V) :
 exists q : Submodule K V, IsCompl p q
· 使用定理 `LinearMap.continuous_of_finiteDimensional`：LinearMap.continuous_of_finit
eDimensional [T2Space E] [FiniteDimensional 𝕜 E] (f : E ->ₗ[𝕜] F') : Continuous 
f
· 使用定理 `Prod.instIsTopologicalAddGroup`：∀ {G : Type w} {H : Type x} [inst : Topo
logicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [inst_3 : Topo
logicalSpace H] [ins…
· 使用定理 `instT2SpaceSubtype`：∀ {X : Type u_1} [inst : TopologicalSpace X] {p : X 
→ Prop} [T2Space X], T2Space (Subtype p)
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.injective_domRestrict_iff`：∀ {R : Type u_1} {R₂ : Type u_2} {M
 : Type u_5} {M₂ : Type u_7} [inst : Ring R] [inst_1 : Ring R₂]   [inst_2 : AddC
ommGroup M] [inst_3 : Add…
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `IsCompl.disjoint`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bou
ndedOrder α] {x y : α}, IsCompl x y → Disjoint x y
· 使用定理 `LinearMap.surjective_domRestrict_iff`：∀ {R : Type u_1} {R₂ : Type u_2} {
M : Type u_4} {M₂ : Type u_5} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst
_2 : AddCommGroup M] [inst…
（共 87 条，此处仅展示前 30 条）

--- 原说明 ---
The image of an additive Haar measure under a surjective linear map is proportio
nal to a given
additive Haar measure. The proportionality factor will be infinite if the linear
 map has a
nontrivial kernel.
-/
theorem LinearMap.exists_map_addHaar_eq_smul_addHaar' (h : Function.Surjective L) :
    ∃ (c : ℝ≥0∞), 0 < c ∧ c < ∞ ∧ μ.map L = (c * addHaar (univ : Set (LinearMap.ker L))) • ν := by
  /- This is true for the second projection in product spaces, as the projection of the Haar
  measure `μS.prod μT` is equal to the Haar measure `μT` multiplied by the total mass of `μS`. This
  is also true for linear equivalences, as they map Haar measure to Haar measure. The general case
  follows from these two and linear algebra, as `L` can be interpreted as the composition of the
  projection `P` on a complement `T` to its kernel `S`, together with a linear equivalence. -/
  have : FiniteDimensional 𝕜 E := .of_locallyCompactSpace 𝕜
  have : ProperSpace F := by
    rcases subsingleton_or_nontrivial E with hE | hE
    · have : Subsingleton F := Function.Surjective.subsingleton h
      infer_instance
    · have : ProperSpace 𝕜 := .of_locallyCompact_module 𝕜 E
      have : FiniteDimensional 𝕜 F := Module.Finite.of_surjective L h
      exact FiniteDimensional.proper 𝕜 F
  let S : Submodule 𝕜 E := LinearMap.ker L
  obtain ⟨T, hT⟩ : ∃ T : Submodule 𝕜 E, IsCompl S T := Submodule.exists_isCompl S
  let M : (S × T) ≃ₗ[𝕜] E := Submodule.prodEquivOfIsCompl S T hT
  have M_cont : Continuous M.symm := LinearMap.continuous_of_finiteDimensional _
  let P : S × T →ₗ[𝕜] T := LinearMap.snd 𝕜 S T
  have P_cont : Continuous P := LinearMap.continuous_of_finiteDimensional _
  have I : Function.Bijective (LinearMap.domRestrict L T) :=
    ⟨LinearMap.injective_domRestrict_iff.2 hT.disjoint.symm,
    (LinearMap.surjective_domRestrict_iff h).2 hT.symm.codisjoint⟩
  let L' : T ≃ₗ[𝕜] F := LinearEquiv.ofBijective (LinearMap.domRestrict L T) I
  have L'_cont : Continuous L' := LinearMap.continuous_of_finiteDimensional _
  have A : L = (L' : T →ₗ[𝕜] F).comp (P.comp (M.symm : E →ₗ[𝕜] (S × T))) := by
    ext x
    obtain ⟨y, z, hyz⟩ : ∃ (y : S) (z : T), M.symm x = (y, z) := ⟨_, _, rfl⟩
    have : x = M (y, z) := by
      rw [← hyz]; simp only [LinearEquiv.apply_symm_apply]
    simp [L', P, M, this]
  have I : μ.map L = ((μ.map M.symm).map P).map L' := by
    rw [Measure.map_map, Measure.map_map, A]
    · rfl
    · exact L'_cont.measurable.comp P_cont.measurable
    · exact M_cont.measurable
    · exact L'_cont.measurable
    · exact P_cont.measurable
  let μS : Measure S := addHaar
  let μT : Measure T := addHaar
  obtain ⟨c₀, c₀_pos, c₀_fin, h₀⟩ :
      ∃ c₀ : ℝ≥0∞, c₀ ≠ 0 ∧ c₀ ≠ ∞ ∧ μ.map M.symm = c₀ • μS.prod μT := by
    have : IsAddHaarMeasure (μ.map M.symm) :=
      M.toContinuousLinearEquiv.symm.isAddHaarMeasure_map μ
    refine ⟨addHaarScalarFactor (μ.map M.symm) (μS.prod μT), ?_, ENNReal.coe_ne_top,
      isAddLeftInvariant_eq_smul _ _⟩
    simpa only [ne_eq, ENNReal.coe_eq_zero] using
      (addHaarScalarFactor_pos_of_isAddHaarMeasure (μ.map M.symm) (μS.prod μT)).ne'
  have J : (μS.prod μT).map P = (μS univ) • μT := map_snd_prod
  obtain ⟨c₁, c₁_pos, c₁_fin, h₁⟩ : ∃ c₁ : ℝ≥0∞, c₁ ≠ 0 ∧ c₁ ≠ ∞ ∧ μT.map L' = c₁ • ν := by
    have : IsAddHaarMeasure (μT.map L') :=
      L'.toContinuousLinearEquiv.isAddHaarMeasure_map μT
    refine ⟨addHaarScalarFactor (μT.map L') ν, ?_, ENNReal.coe_ne_top,
      isAddLeftInvariant_eq_smul _ _⟩
    simpa only [ne_eq, ENNReal.coe_eq_zero] using
      (addHaarScalarFactor_pos_of_isAddHaarMeasure (μT.map L') ν).ne'
  refine ⟨c₀ * c₁, by simp [pos_iff_ne_zero, c₀_pos, c₁_pos],
    ENNReal.mul_lt_top c₀_fin.lt_top c₁_fin.lt_top, ?_⟩
  simp only [I, h₀, Measure.map_smul, J, smul_smul, h₁]
  rw [mul_assoc, mul_comm _ c₁, ← mul_assoc]

/-- The image of an additive Haar measure under a surjective linear map is proportional to a given
additive Haar measure, with a positive (but maybe infinite) factor. -/
/-
**LinearMap.exists_map_addHaar_eq_smul_addHaar** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.exists_map_addHaar_eq_smul_addHaar (h : Function.Surjective L) :
 exists (c : Real>=0∞), 0 < c ∧ μ.map L = c • ν
参数：h : Function.Surjective L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceSubtypeMemSubmoduleOfCompleteSpaceOfLocallyCompactSpace`：
∀ {𝕜 : Type u_1} {E : Type u_2} [inst : NontriviallyNormedField 𝕜] [CompleteSpac
e 𝕜] [inst_2 : NormedAddCommGroup E]   [inst_3 : NormedSpace…
· 使用定理 `LinearMap.exists_map_addHaar_eq_smul_addHaar'`：LinearMap.exists_map_addH
aar_eq_smul_addHaar' (h : Function.Surjective L) : exists (c : Real>=0∞), 0 < c 
∧ c < ∞ ∧ μ.map L = (c * addHaar (u…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.instNoZeroDivisors`：NoZeroDivisors ENNReal
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `MeasureTheory.Measure.instNeZeroOfNonempty`：∀ {X : Type u_1} [inst : Top
ologicalSpace X] {m : MeasurableSpace X} (μ : MeasureTheory.Measure X) [μ.IsOpen
PosMeasure]   [Nonempty X], NeZe…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsOpenPosMeasure`：∀ {G : Type u
_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpace 
G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `MeasureTheory.Measure.isAddHaarMeasure_addHaarMeasure`：∀ {G : Type u_1} 
[inst : AddGroup G] [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalAddGrou
p G]   [inst_3 : MeasurableSpace G] [inst_4…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p

--- 原说明 ---
The image of an additive Haar measure under a surjective linear map is proportio
nal to a given
additive Haar measure, with a positive (but maybe infinite) factor.
-/
theorem LinearMap.exists_map_addHaar_eq_smul_addHaar (h : Function.Surjective L) :
    ∃ (c : ℝ≥0∞), 0 < c ∧ μ.map L = c • ν := by
  rcases L.exists_map_addHaar_eq_smul_addHaar' μ ν h with ⟨c, c_pos, -, hc⟩
  exact ⟨_, by simp [c_pos, NeZero.ne addHaar], hc⟩

namespace MeasureTheory

/-- Given a surjective linear map `L`, it is equivalent to require a property almost everywhere
in the source or the target spaces of `L`, with respect to additive Haar measures there. -/
/-
**MeasureTheory.ae_comp_linearMap_mem_iff** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：ae_comp_linearMap_mem_iff (h : Function.Surjective L) {s : Set F} (hs : Me
asurableSet s) : (forallᵐ x ∂μ, L x in s) ↔ forallᵐ y ∂ν, y in s
参数：h : Function.Surjective L；hs : MeasurableSet s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteDimensional.of_locallyCompactSpace`：FiniteDimensional.of_locallyCo
mpactSpace [WeaklyLocallyCompactSpace E] : FiniteDimensional 𝕜 E
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `Continuous.aemeasurable`：Continuous.aemeasurable {f : α -> γ} (h : Conti
nuous f) {μ : Measure α} : AEMeasurable f μ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `LinearMap.continuous_of_finiteDimensional`：LinearMap.continuous_of_finit
eDimensional [T2Space E] [FiniteDimensional 𝕜 E] (f : E ->ₗ[𝕜] F') : Continuous 
f
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `MeasureTheory.ae_map_iff`：ae_map_iff {f : α -> β} (hf : AEMeasurable f μ
) {p : β -> Prop} (hp : MeasurableSet { x | p x }) : (forallᵐ y ∂μ.map f, p y) ↔
 forallᵐ x ∂μ,…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearMap.exists_map_addHaar_eq_smul_addHaar`：LinearMap.exists_map_addHa
ar_eq_smul_addHaar (h : Function.Surjective L) : exists (c : Real>=0∞), 0 < c ∧ 
μ.map L = c • ν
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.ae_ennreal_smul_measure_iff`：ae_ennreal_smul_measu
re_iff {c : Real>=0∞} {p : α -> Prop} (hc : c != 0) {μ : Measure α} : (forallᵐ x
 ∂c • μ, p x) ↔ forallᵐ x ∂μ, p x
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b

--- 原说明 ---
Given a surjective linear map `L`, it is equivalent to require a property almost
 everywhere
in the source or the target spaces of `L`, with respect to additive Haar measure
s there.
-/
lemma ae_comp_linearMap_mem_iff (h : Function.Surjective L) {s : Set F} (hs : MeasurableSet s) :
    (∀ᵐ x ∂μ, L x ∈ s) ↔ ∀ᵐ y ∂ν, y ∈ s := by
  have : FiniteDimensional 𝕜 E := .of_locallyCompactSpace 𝕜
  have : AEMeasurable L μ := L.continuous_of_finiteDimensional.aemeasurable
  apply (ae_map_iff this hs).symm.trans
  rcases L.exists_map_addHaar_eq_smul_addHaar μ ν h with ⟨c, c_pos, hc⟩
  rw [hc]
  exact ae_ennreal_smul_measure_iff c_pos.ne'

/-- Given a linear map `L : E → F`, a property holds almost everywhere in `F` if and only if,
almost everywhere in `F`, it holds almost everywhere along the subspace spanned by the
image of `L`. This is an instance of a disintegration argument for additive Haar measures. -/
/-
**MeasureTheory.ae_ae_add_linearMap_mem_iff** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTh
eory`。
形式化陈述：ae_ae_add_linearMap_mem_iff [LocallyCompactSpace F] {s : Set F} (hs : Meas
urableSet s) : (forallᵐ y ∂ν, forallᵐ x ∂μ, y + L x in s) ↔ forallᵐ y ∂ν, y in s
参数：hs : MeasurableSet s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteDimensional.of_locallyCompactSpace`：FiniteDimensional.of_locallyCo
mpactSpace [WeaklyLocallyCompactSpace E] : FiniteDimensional 𝕜 E
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用引理 `ProperSpace.of_locallyCompactSpace`：ProperSpace.of_locallyCompactSpace (
𝕜 : Type*) [NontriviallyNormedField 𝕜] {E : Type*} [SeminormedAddCommGroup E] [N
ormedSpace 𝕜 E] [Locally…
· 使用定理 `LinearMap.continuous_of_finiteDimensional`：LinearMap.continuous_of_finit
eDimensional [T2Space E] [FiniteDimensional 𝕜 E] (f : E ->ₗ[𝕜] F') : Continuous 
f
· 使用定理 `Prod.instIsTopologicalAddGroup`：∀ {G : Type w} {H : Type x} [inst : Topo
logicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [inst_3 : Topo
logicalSpace H] [ins…
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.range_coprod`：range_coprod (f : M ->ₗ[R] M₃) (g : M₂ ->ₗ[R] M₃
) : range (f.coprod g) = range f ⊔ range g
· 使用定理 `LinearMap.range_id`：range_id : range (LinearMap.id : M ->ₗ[R] M) = ⊤
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.ae_comp_linearMap_mem_iff`：ae_comp_linearMap_mem_iff (h : 
Function.Surjective L) {s : Set F} (hs : MeasurableSet s) : (forallᵐ x ∂μ, L x i
n s) ↔ forallᵐ y ∂ν, y in s
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `MeasureTheory.Measure.prod.instIsAddHaarMeasure`：∀ {G : Type u_3} [inst 
: AddGroup G] [inst_1 : TopologicalSpace G] {x : MeasurableSpace G} {H : Type u_
4}   [inst_2 : AddGroup H] [inst_3 : …
（共 41 条，此处仅展示前 30 条）

--- 原说明 ---
Given a linear map `L : E → F`, a property holds almost everywhere in `F` if and
 only if,
almost everywhere in `F`, it holds almost everywhere along the subspace spanned 
by the
image of `L`. This is an instance of a disintegration argument for additive Haar
 measures.
-/
lemma ae_ae_add_linearMap_mem_iff [LocallyCompactSpace F] {s : Set F} (hs : MeasurableSet s) :
    (∀ᵐ y ∂ν, ∀ᵐ x ∂μ, y + L x ∈ s) ↔ ∀ᵐ y ∂ν, y ∈ s := by
  have : FiniteDimensional 𝕜 E := .of_locallyCompactSpace 𝕜
  have : FiniteDimensional 𝕜 F := .of_locallyCompactSpace 𝕜
  have : ProperSpace E := .of_locallyCompactSpace 𝕜
  have : ProperSpace F := .of_locallyCompactSpace 𝕜
  let M : F × E →ₗ[𝕜] F := LinearMap.id.coprod L
  have M_cont : Continuous M := M.continuous_of_finiteDimensional
  -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to change `range_eq_top` into
  -- `range_eq_top (f := _)`
  have hM : Function.Surjective M := by
    simp [M, ← LinearMap.range_eq_top (f := _), LinearMap.range_coprod]
  have A : ∀ x, M x ∈ s ↔ x ∈ M ⁻¹' s := fun x ↦ Iff.rfl
  simp_rw [← ae_comp_linearMap_mem_iff M (ν.prod μ) ν hM hs, A]
  rw [Measure.ae_prod_mem_iff_ae_ae_mem]
  · simp only [M, mem_preimage, LinearMap.coprod_apply, LinearMap.id_coe, id_eq]
  · exact M_cont.measurable hs

/-- To check that a property holds almost everywhere with respect to an additive Haar measure, it
suffices to check it almost everywhere along all translates of a given vector subspace. This is an
/-
**MeasureTheory.of** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance of a disintegration argument for additive Haar measures. -/
/-
**MeasureTheory.ae_mem_of_ae_add_linearMap_mem** 是 Mathlib 中的一个引理，位于命名空间 `Measur
eTheory`。
形式化陈述：ae_mem_of_ae_add_linearMap_mem [LocallyCompactSpace F] {s : Set F} (hs : M
easurableSet s) (h : forall y, forallᵐ x ∂μ, y + L x in s) : forallᵐ y ∂ν, y in 
s
参数：hs : MeasurableSet s；h : forall y, forallᵐ x ∂μ, y + L x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `MeasureTheory.ae_ae_add_linearMap_mem_iff`：ae_ae_add_linearMap_mem_iff [
LocallyCompactSpace F] {s : Set F} (hs : MeasurableSet s) : (forallᵐ y ∂ν, foral
lᵐ x ∂μ, y + L x in s) ↔ forall…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x

--- 原说明 ---
To check that a property holds almost everywhere with respect to an additive Haa
r measure, it
suffices to check it almost everywhere along all translates of a given vector su
bspace. This is an
instance of a disintegration argument for additive Haar measures.
-/
lemma ae_mem_of_ae_add_linearMap_mem [LocallyCompactSpace F] {s : Set F} (hs : MeasurableSet s)
    (h : ∀ y, ∀ᵐ x ∂μ, y + L x ∈ s) : ∀ᵐ y ∂ν, y ∈ s :=
  (ae_ae_add_linearMap_mem_iff L μ ν hs).1 (Filter.Eventually.of_forall h)

end MeasureTheory

