/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Yury Kudryashov, Frédéric Dupuis
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
public import Mathlib.Topology.Algebra.Module.Equiv

/-! # Infinite sums in topological vector spaces -/

@[expose] public section

variable {α β γ δ : Type*}

open Filter Finset Function

section ConstSMul

variable [TopologicalSpace α] [AddCommMonoid α] [DistribSMul γ α]
  [ContinuousConstSMul γ α] {f : β -> α} {L : SummationFilter β}

/--
theorem `HasSum.const_smul` / 定理 `HasSum.const_smul`

English:
theorem HasSum.const_smul
  given: {a : α} (b : γ) (hf : HasSum f a L)
  proof: hf.map (DistribSMul.toAddMonoidHom α _) continuous_const_smul _

中文:
定理 HasSum.const_smul
  条件: {a : α} (b : γ) (hf : HasSum f a L)
  证明: hf.map (DistribSMul.toAddMonoidHom α _) continuous_const_smul _

Depends on / 依赖: DistribSMul, DistribSMul.toAddMonoidHom, continuous_const_smul, hf.map, toAddMonoidHom
-/
theorem HasSum.const_smul {a : α} (b : γ) (hf : HasSum f a L) :
    HasSum (fun i => b • f i) (b • a) L :=
hf.map (DistribSMul.toAddMonoidHom α _) continuous_const_smul _

/--
theorem `Summable.const_smul` / 定理 `Summable.const_smul`

English:
theorem Summable.const_smul
  given: (b : γ) (hf : Summable f L)
  statement: Summable (fun i => b • f i) L
  proof: (hf.hasSum.const_smul _).summable

中文:
定理 Summable.const_smul
  条件: (b : γ) (hf : Summable f L)
  结论: Summable (fun i => b • f i) L
  证明: (hf.hasSum.const_smul _).summable

Depends on / 依赖: const_smul, hasSum, hf.hasSum.const_smul, summable
-/
theorem Summable.const_smul (b : γ) (hf : Summable f L) : Summable (fun i => b • f i) L :=
  (hf.hasSum.const_smul _).summable

/--
theorem `Summable.tsum_const_smul` / 定理 `Summable.tsum_const_smul`

English:
theorem Summable.tsum_const_smul
  given: [T2Space α] [L.NeBot] (b : γ) (hf : Summable f L)
  proof: (hf.hasSum.const_smul _).tsum_eq

中文:
定理 Summable.tsum_const_smul
  条件: [T2Space α] [L.NeBot] (b : γ) (hf : Summable f L)
  证明: (hf.hasSum.const_smul _).tsum_eq
-/
protected theorem Summable.tsum_const_smul [T2Space α] [L.NeBot] (b : γ) (hf : Summable f L) :
    ∑'[L] i, b • f i = b • ∑'[L] i, f i :=
  (hf.hasSum.const_smul _).tsum_eq

/--
lemma `tsum_const_smul'` / 引理 `tsum_const_smul'`

English:
lemma tsum_const_smul'
  statement: {γ : Type*} [Group γ] [DistribMulAction γ α] [ContinuousConstSMul γ α]
  proof: ((Homeomorph.smul g).isClosedEmbedding.map_tsum f (g := show α ≃+ α from
    { DistribSMul.toAddMonoidHom _ g with
      invFun := DistribSMul.toAddMonoidHom _ g⁻¹
      left_inv a := by simp, right_inv a := by simp })).symm

中文:
引理 tsum_const_smul'
  结论: {γ : 类型} [Group γ] [DistribMulAction γ α] [ContinuousConstSMul γ α]
  证明: ((Homeomorph.smul g).isClosedEmbedding.map_tsum f (g := show α ≃+ α from
    { DistribSMul.toAddMonoidHom _ g with
      invFun := DistribSMul.toAddMonoidHom _ g⁻¹
      left_inv a := by simp, right_inv a := by simp })).symm

Depends on / 依赖: DistribSMul, DistribSMul.toAddMonoidHom, Homeomorph, Homeomorph.smul, invFun, isClosedEmbedding, isClosedEmbedding.map_tsum, left_inv, map_tsum, right_inv, toAddMonoidHom
-/
lemma tsum_const_smul' {γ : Type*} [Group γ] [DistribMulAction γ α] [ContinuousConstSMul γ α]
    [T2Space α] (g : γ) :
    ∑'[L] (i : β), g • f i = g • ∑'[L] (i : β), f i :=
  ((Homeomorph.smul g).isClosedEmbedding.map_tsum f (g := show α ≃+ α from
    { DistribSMul.toAddMonoidHom _ g with
      invFun := DistribSMul.toAddMonoidHom _ g⁻¹
      left_inv a := by simp, right_inv a := by simp })).symm

/--
lemma `tsum_const_smul''` / 引理 `tsum_const_smul''`

English:
lemma tsum_const_smul''
  statement: {γ : Type*} [DivisionSemiring γ] [Module γ α] [ContinuousConstSMul γ α]
  proof: by
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  · exact tsum_const_smul' (Units.mk0 g hg)

中文:
引理 tsum_const_smul''
  结论: {γ : 类型} [DivisionSemiring γ] [Module γ α] [ContinuousConstSMul γ α]
  证明: by
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  · exact tsum_const_smul' (Units.mk0 g hg)

Depends on / 依赖: Units.mk0, eq_or_ne, tsum_const_smul
-/
lemma tsum_const_smul'' {γ : Type*} [DivisionSemiring γ] [Module γ α] [ContinuousConstSMul γ α]
    [T2Space α] (g : γ) :
    ∑'[L] (i : β), g • f i = g • ∑'[L] (i : β), f i := by
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  · exact tsum_const_smul' (Units.mk0 g hg)

end ConstSMul



variable {ι κ R R₂ M M₂ : Type*}

section SMulConst

variable [Semiring R] [TopologicalSpace R] [TopologicalSpace M] [AddCommMonoid M] [Module R M]
  [ContinuousSMul R M] {f : ι -> R} {L : SummationFilter ι}

/--
theorem `HasSum.smul_const` / 定理 `HasSum.smul_const`

English:
theorem HasSum.smul_const
  given: {r : R} (hf : HasSum f r L) (a : M)
  proof: hf.map ((smulAddHom R M).flip a) (continuous_id.smul continuous_const)

中文:
定理 HasSum.smul_const
  条件: {r : R} (hf : HasSum f r L) (a : M)
  证明: hf.map ((smulAddHom R M).flip a) (continuous_id.smul continuous_const)

Depends on / 依赖: continuous_const, continuous_id, continuous_id.smul, hf.map, smulAddHom
-/
theorem HasSum.smul_const {r : R} (hf : HasSum f r L) (a : M) :
    HasSum (fun z => f z • a) (r • a) L :=
  hf.map ((smulAddHom R M).flip a) (continuous_id.smul continuous_const)

/--
theorem `Summable.smul_const` / 定理 `Summable.smul_const`

English:
theorem Summable.smul_const
  given: (hf : Summable f L) (a : M)
  statement: Summable (fun z => f z • a) L
  proof: (hf.hasSum.smul_const _).summable

中文:
定理 Summable.smul_const
  条件: (hf : Summable f L) (a : M)
  结论: Summable (fun z => f z • a) L
  证明: (hf.hasSum.smul_const _).summable

Depends on / 依赖: hasSum, hf.hasSum.smul_const, smul_const, summable
-/
theorem Summable.smul_const (hf : Summable f L) (a : M) : Summable (fun z => f z • a) L :=
  (hf.hasSum.smul_const _).summable

/--
theorem `Summable.tsum_smul_const` / 定理 `Summable.tsum_smul_const`

English:
theorem Summable.tsum_smul_const
  given: [T2Space M] [L.NeBot] (hf : Summable f L) (a : M)
  proof: (hf.hasSum.smul_const _).tsum_eq

中文:
定理 Summable.tsum_smul_const
  条件: [T2Space M] [L.NeBot] (hf : Summable f L) (a : M)
  证明: (hf.hasSum.smul_const _).tsum_eq
-/
protected theorem Summable.tsum_smul_const [T2Space M] [L.NeBot] (hf : Summable f L) (a : M) :
    ∑'[L] z, f z • a = (∑'[L] z, f z) • a :=
  (hf.hasSum.smul_const _).tsum_eq

end SMulConst

/-!
Note we cannot derive the `mul` lemmas from these `smul` lemmas, as the `mul` versions do not
require associativity, but `Module` does.
-/
section tsum_smul_tsum

variable [Semiring R] [AddCommMonoid M] [Module R M]
variable [TopologicalSpace R] [TopologicalSpace M] [T3Space M]
variable [ContinuousAdd M] [ContinuousSMul R M]
variable {f : ι -> R} {g : κ -> M} {s : R} {t u : M}

/--
theorem `HasSum.smul_eq` / 定理 `HasSum.smul_eq`

English:
theorem HasSum.smul_eq
  statement: (hf : HasSum f s) (hg : HasSum g t)
  proof: have key₁ : HasSum (fun i => f i • t) (s • t) := hf.smul_const t
  have : forall i : ι, HasSum (fun c : κ => f i • g c) (f i • t) := fun i => hg.const_smul (f i)
  have key₂ : HasSum (fun i => f i • t) u := HasSum.prod_fiberwise hfg this
  key₁.unique key₂

中文:
定理 HasSum.smul_eq
  结论: (hf : HasSum f s) (hg : HasSum g t)
  证明: have key₁ : HasSum (fun i => f i • t) (s • t) := hf.smul_const t
  have : forall i : ι, HasSum (fun c : κ => f i • g c) (f i • t) := fun i => hg.const_smul (f i)
  have key₂ : HasSum (fun i => f i • t) u := HasSum.prod_fiberwise hfg this
  key₁.unique key₂

Depends on / 依赖: HasSum, HasSum.prod_fiberwise, const_smul, hf.smul_const, hg.const_smul, prod_fiberwise, smul_const, unique
-/
theorem HasSum.smul_eq (hf : HasSum f s) (hg : HasSum g t)
    (hfg : HasSum (fun x : ι × κ => f x.1 • g x.2) u) : s • t = u :=
  have key₁ : HasSum (fun i => f i • t) (s • t) := hf.smul_const t
  have : forall i : ι, HasSum (fun c : κ => f i • g c) (f i • t) := fun i => hg.const_smul (f i)
  have key₂ : HasSum (fun i => f i • t) u := HasSum.prod_fiberwise hfg this
  key₁.unique key₂

/--
theorem `HasSum.smul` / 定理 `HasSum.smul`

English:
theorem HasSum.smul
  statement: (hf : HasSum f s) (hg : HasSum g t)
  proof: let ⟨_u, hu⟩ := hfg
  (hf.smul_eq hg hu).symm ▸ hu

中文:
定理 HasSum.smul
  结论: (hf : HasSum f s) (hg : HasSum g t)
  证明: let ⟨_u, hu⟩ := hfg
  (hf.smul_eq hg hu).symm ▸ hu

Depends on / 依赖: hf.smul_eq, smul_eq
-/
theorem HasSum.smul (hf : HasSum f s) (hg : HasSum g t)
    (hfg : Summable fun x : ι × κ => f x.1 • g x.2) :
    HasSum (fun x : ι × κ => f x.1 • g x.2) (s • t) :=
  let ⟨_u, hu⟩ := hfg
  (hf.smul_eq hg hu).symm ▸ hu

/--
theorem `tsum_smul_tsum` / 定理 `tsum_smul_tsum`

English:
theorem tsum_smul_tsum
  statement: (hf : Summable f) (hg : Summable g)
  proof: hf.hasSum.smul_eq hg.hasSum hfg.hasSum

中文:
定理 tsum_smul_tsum
  结论: (hf : Summable f) (hg : Summable g)
  证明: hf.hasSum.smul_eq hg.hasSum hfg.hasSum

Depends on / 依赖: hasSum, hf.hasSum.smul_eq, hfg.hasSum, hg.hasSum, smul_eq
-/
theorem tsum_smul_tsum (hf : Summable f) (hg : Summable g)
    (hfg : Summable fun x : ι × κ => f x.1 • g x.2) :
    ((∑' x, f x) • ∑' y, g y) = ∑' z : ι × κ, f z.1 • g z.2 :=
  hf.hasSum.smul_eq hg.hasSum hfg.hasSum

end tsum_smul_tsum

section HasSum

-- Results in this section hold for continuous additive monoid homomorphisms or equivalences but we
-- don't have bundled continuous additive homomorphisms.
variable [Semiring R] [Semiring R₂] [AddCommMonoid M] [Module R M] [AddCommMonoid M₂] [Module R₂ M₂]
  [TopologicalSpace M] [TopologicalSpace M₂] {σ : R ->+* R₂} {σ' : R₂ ->+* R} [RingHomInvPair σ σ']
  [RingHomInvPair σ' σ] {L : SummationFilter ι}

/--
theorem `ContinuousLinearMap.hasSum` / 定理 `ContinuousLinearMap.hasSum`

English:
theorem ContinuousLinearMap.hasSum
  statement: {f : ι -> M} (φ : M ->SL[σ] M₂) {x : M}
  proof: by
  simpa only using! hf.map φ.toLinearMap.toAddMonoidHom φ.continuous

alias HasSum.mapL := ContinuousLinearMap.hasSum

中文:
定理 ContinuousLinearMap.hasSum
  结论: {f : ι -> M} (φ : M ->SL[σ] M₂) {x : M}
  证明: by
  simpa only using! hf.map φ.toLinearMap.toAddMonoidHom φ.continuous

alias HasSum.mapL := ContinuousLinearMap.hasSum
-/
protected theorem ContinuousLinearMap.hasSum {f : ι -> M} (φ : M ->SL[σ] M₂) {x : M}
    (hf : HasSum f x L) : HasSum (fun b : ι => φ (f b)) (φ x) L := by
  simpa only using! hf.map φ.toLinearMap.toAddMonoidHom φ.continuous

alias HasSum.mapL := ContinuousLinearMap.hasSum

/--
theorem `ContinuousLinearMap.summable` / 定理 `ContinuousLinearMap.summable`

English:
theorem ContinuousLinearMap.summable
  given: {f : ι -> M} (φ : M ->SL[σ] M₂) (hf : Summable f L)
  proof: (hf.hasSum.mapL φ).summable

alias Summable.mapL := ContinuousLinearMap.summable

中文:
定理 ContinuousLinearMap.summable
  条件: {f : ι -> M} (φ : M ->SL[σ] M₂) (hf : Summable f L)
  证明: (hf.hasSum.mapL φ).summable

alias Summable.mapL := ContinuousLinearMap.summable
-/
protected theorem ContinuousLinearMap.summable {f : ι -> M} (φ : M ->SL[σ] M₂) (hf : Summable f L) :
    Summable (fun b : ι => φ (f b)) L :=
  (hf.hasSum.mapL φ).summable

alias Summable.mapL := ContinuousLinearMap.summable

/--
theorem `ContinuousLinearMap.map_tsum` / 定理 `ContinuousLinearMap.map_tsum`

English:
theorem ContinuousLinearMap.map_tsum
  statement: [T2Space M₂] [L.NeBot] {f : ι -> M} (φ : M ->SL[σ] M₂)
  proof: (hf.hasSum.mapL φ).tsum_eq.symm

中文:
定理 ContinuousLinearMap.map_tsum
  结论: [T2Space M₂] [L.NeBot] {f : ι -> M} (φ : M ->SL[σ] M₂)
  证明: (hf.hasSum.mapL φ).tsum_eq.symm
-/
protected theorem ContinuousLinearMap.map_tsum [T2Space M₂] [L.NeBot] {f : ι -> M} (φ : M ->SL[σ] M₂)
    (hf : Summable f L) : φ (∑'[L] z, f z) = ∑'[L] z, φ (f z) :=
  (hf.hasSum.mapL φ).tsum_eq.symm

/--
theorem `ContinuousLinearEquiv.hasSum` / 定理 `ContinuousLinearEquiv.hasSum`

English:
theorem ContinuousLinearEquiv.hasSum
  given: {f : ι -> M} (e : M ≃SL[σ] M₂) {y : M₂}
  proof: ⟨fun h => by simpa only [e.symm.coe_coe, e.symm_apply_apply] using h.mapL (e.symm : M₂ ->SL[σ'] M),
    fun h => by simpa only [e.coe_coe, e.apply_symm_apply] using (e : M ->SL[σ] M₂).hasSum h⟩

中文:
定理 ContinuousLinearEquiv.hasSum
  条件: {f : ι -> M} (e : M ≃SL[σ] M₂) {y : M₂}
  证明: ⟨fun h => by simpa only [e.symm.coe_coe, e.symm_apply_apply] using h.mapL (e.symm : M₂ ->SL[σ'] M),
    fun h => by simpa only [e.coe_coe, e.apply_symm_apply] using (e : M ->SL[σ] M₂).hasSum h⟩
-/
protected theorem ContinuousLinearEquiv.hasSum {f : ι -> M} (e : M ≃SL[σ] M₂) {y : M₂} :
    HasSum (fun b : ι => e (f b)) y L ↔ HasSum f (e.symm y) L :=
  ⟨fun h => by simpa only [e.symm.coe_coe, e.symm_apply_apply] using h.mapL (e.symm : M₂ ->SL[σ'] M),
    fun h => by simpa only [e.coe_coe, e.apply_symm_apply] using (e : M ->SL[σ] M₂).hasSum h⟩

/--
theorem `ContinuousLinearEquiv.hasSum'` / 定理 `ContinuousLinearEquiv.hasSum'`

English:
theorem ContinuousLinearEquiv.hasSum'
  given: {f : ι -> M} (e : M ≃SL[σ] M₂) {x : M}
  proof: by
  rw [e.hasSum]; rw [ContinuousLinearEquiv.symm_apply_apply]

中文:
定理 ContinuousLinearEquiv.hasSum'
  条件: {f : ι -> M} (e : M ≃SL[σ] M₂) {x : M}
  证明: by
  rw [e.hasSum]; rw [ContinuousLinearEquiv.symm_apply_apply]
-/
protected theorem ContinuousLinearEquiv.hasSum' {f : ι -> M} (e : M ≃SL[σ] M₂) {x : M} :
    HasSum (fun b : ι => e (f b)) (e x) L ↔ HasSum f x L := by
  rw [e.hasSum]; rw [ContinuousLinearEquiv.symm_apply_apply]

/--
theorem `ContinuousLinearEquiv.summable` / 定理 `ContinuousLinearEquiv.summable`

English:
theorem ContinuousLinearEquiv.summable
  given: {f : ι -> M} (e : M ≃SL[σ] M₂)
  proof: ⟨fun hf => (e.hasSum.1 hf.hasSum).summable, (e : M ->SL[σ] M₂).summable⟩

中文:
定理 ContinuousLinearEquiv.summable
  条件: {f : ι -> M} (e : M ≃SL[σ] M₂)
  证明: ⟨fun hf => (e.hasSum.1 hf.hasSum).summable, (e : M ->SL[σ] M₂).summable⟩
-/
protected theorem ContinuousLinearEquiv.summable {f : ι -> M} (e : M ≃SL[σ] M₂) :
    (Summable (fun b : ι => e (f b)) L) ↔ Summable f L :=
  ⟨fun hf => (e.hasSum.1 hf.hasSum).summable, (e : M ->SL[σ] M₂).summable⟩

/--
theorem `ContinuousLinearEquiv.tsum_eq_iff` / 定理 `ContinuousLinearEquiv.tsum_eq_iff`

English:
theorem ContinuousLinearEquiv.tsum_eq_iff
  statement: [T2Space M] [T2Space M₂]
  proof: by
  by_cases hf : Summable f L
  · by_cases hL : L.NeBot
    · exact ⟨fun h => (e.hasSum.mp ((e.summable.mpr hf).hasSum_iff.mpr h)).tsum_eq, fun h =>
        (e.hasSum.mpr (hf.hasSum_iff.mpr h)).tsum_eq⟩
    · simp only [tsum_bot hL, eq_symm_apply]
      constructor <;> rintro rfl
      exacts [e.m

中文:
定理 ContinuousLinearEquiv.tsum_eq_iff
  结论: [T2Space M] [T2Space M₂]
  证明: by
  by_cases hf : Summable f L
  · by_cases hL : L.NeBot
    · exact ⟨fun h => (e.hasSum.mp ((e.summable.mpr hf).hasSum_iff.mpr h)).tsum_eq, fun h =>
        (e.hasSum.mpr (hf.hasSum_iff.mpr h)).tsum_eq⟩
    · simp only [tsum_bot hL, eq_symm_apply]
      constructor <;> rintro rfl
      exacts [e.m

Depends on / 依赖: L.NeBot, Summable, e.hasSum.mp, e.hasSum.mpr, e.map_finsum, e.summable.mp, e.summable.mpr, eq_symm_apply, exacts, hasSum, hasSum_iff, hasSum_iff.mpr, hf.hasSum_iff.mpr, map_finsum, summable, tsum_bot, tsum_eq, tsum_eq_zero_of_not_summable
-/
theorem ContinuousLinearEquiv.tsum_eq_iff [T2Space M] [T2Space M₂]
    {f : ι -> M} (e : M ≃SL[σ] M₂) {y : M₂} :
    (∑'[L] z, e (f z)) = y ↔ ∑'[L] z, f z = e.symm y := by
  by_cases hf : Summable f L
  · by_cases hL : L.NeBot
    · exact ⟨fun h => (e.hasSum.mp ((e.summable.mpr hf).hasSum_iff.mpr h)).tsum_eq, fun h =>
        (e.hasSum.mpr (hf.hasSum_iff.mpr h)).tsum_eq⟩
    · simp only [tsum_bot hL, eq_symm_apply]
      constructor <;> rintro rfl
      exacts [e.map_finsum f, (e.map_finsum f).symm]
  · have hf' : ¬Summable (fun z => e (f z)) L := fun h => hf (e.summable.mp h)
    rw [tsum_eq_zero_of_not_summable hf]; rw [tsum_eq_zero_of_not_summable hf']
    refine ⟨?_, fun H => ?_⟩
    · rintro rfl
      simp
    · simpa using congr_arg (fun z => e z) H

/--
theorem `ContinuousLinearEquiv.map_tsum` / 定理 `ContinuousLinearEquiv.map_tsum`

English:
theorem ContinuousLinearEquiv.map_tsum
  statement: [T2Space M] [T2Space M₂]
  proof: by
  refine symm (e.tsum_eq_iff.mpr ?_)
  rw [e.symm_apply_apply _]

中文:
定理 ContinuousLinearEquiv.map_tsum
  结论: [T2Space M] [T2Space M₂]
  证明: by
  refine symm (e.tsum_eq_iff.mpr ?_)
  rw [e.symm_apply_apply _]
-/
protected theorem ContinuousLinearEquiv.map_tsum [T2Space M] [T2Space M₂]
    {f : ι -> M} (e : M ≃SL[σ] M₂) : e (∑'[L] z, f z) = ∑'[L] z, e (f z) := by
  refine symm (e.tsum_eq_iff.mpr ?_)
  rw [e.symm_apply_apply _]

end HasSum



section automorphize

variable {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [T2Space M] {R : Type*}
  [DivisionRing R] [Module R M] [ContinuousConstSMul R M]

/-- Given a group `α` acting on a type `β`, and a function `f : β → M`, we "automorphize" `f` to a
  function `β ⧸ α → M` by summing over `α` orbits, `b ↦ ∑' (a : α), f(a • b)`. -/
@[to_additive /-- Given an additive group `α` acting on a type `β`, and a function `f : β → M`,
  we automorphize `f` to a function `β ⧸ α → M` by summing over `α` orbits,
  `b ↦ ∑' (a : α), f(a • b)`. -/]
/--
Definition of `MulAction.automorphize` / `MulAction.automorphize` 的定义

English:
definition MulAction.automorphize
  signature: [Group α] [MulAction α β] (f : β -> M)
  body: by
  refine @Quotient.lift _ _ (_) (fun b => ∑' (a : α), f (a • b)) ?_
  intro b₁ b₂ ⟨a, (ha : a • b₂ = b₁)⟩
  rw [← ha]
  convert! (Equiv.mulRight a).tsum_eq (fun a' => f (a' • b₂)) using 1
  simp only [Equiv.coe_mulRight]
  congr
  ext
  congr 1
  simp only [mul_smul]

中文:
定义 MulAction.automorphize
  签名: [Group α] [MulAction α β] (f : β -> M)
  定义体: by
  refine @Quotient.lift _ _ (_) (fun b => ∑' (a : α), f (a • b)) ?_
  intro b₁ b₂ ⟨a, (ha : a • b₂ = b₁)⟩
  rw [← ha]
  convert! (Equiv.mulRight a).tsum_eq (fun a' => f (a' • b₂)) using 1
  simp only [Equiv.coe_mulRight]
  congr
  ext
  congr 1
  simp only [mul_smul]

Depends on / 依赖: Equiv.coe_mulRight, Equiv.mulRight, Quotient, Quotient.lift, coe_mulRight, convert, mulRight, mul_smul, tsum_eq
-/
noncomputable def MulAction.automorphize [Group α] [MulAction α β] (f : β -> M) :
    Quotient (MulAction.orbitRel α β) -> M := by
  refine @Quotient.lift _ _ (_) (fun b => ∑' (a : α), f (a • b)) ?_
  intro b₁ b₂ ⟨a, (ha : a • b₂ = b₁)⟩
  rw [← ha]
  convert! (Equiv.mulRight a).tsum_eq (fun a' => f (a' • b₂)) using 1
  simp only [Equiv.coe_mulRight]
  congr
  ext
  congr 1
  simp only [mul_smul]

/-- Automorphization of a function into an `R`-`Module` distributes, that is, commutes with the
`R`-scalar multiplication. -/
@[to_additive (dont_translate := R) automorphize_smul_left /--
Automorphization of a function into an `R`-`Module` distributes, that is, commutes with the
`R`-scalar multiplication. -/]
/--
lemma `MulAction.automorphize_smul_left` / 引理 `MulAction.automorphize_smul_left`

English:
lemma MulAction.automorphize_smul_left
  statement: [Group α] [MulAction α β] (f : β -> M)
  proof: by
  ext x
  induction x using Quotient.inductionOn with | _ b
  simp only [automorphize, Pi.smul_apply', comp_apply]
  set π : β -> Quotient (MulAction.orbitRel α β) := Quotient.mk (MulAction.orbitRel α β)
  have H₁ : forall a : α, π (a • b) = π b := by
    intro a
    apply (@Quotient.eq _ (MulAct

中文:
引理 MulAction.automorphize_smul_left
  结论: [Group α] [MulAction α β] (f : β -> M)
  证明: by
  ext x
  induction x using Quotient.inductionOn with | _ b
  simp only [automorphize, Pi.smul_apply', comp_apply]
  set π : β -> Quotient (MulAction.orbitRel α β) := Quotient.mk (MulAction.orbitRel α β)
  have H₁ : forall a : α, π (a • b) = π b := by
    intro a
    apply (@Quotient.eq _ (MulAct

Depends on / 依赖: MulAction, MulAction.orbitRel, Pi.smul_apply, Quotient, Quotient.eq, Quotient.inductionOn, Quotient.mk, automorphize, comp_apply, inductionOn, orbitRel, simp_rw, smul_apply, tsum_const_smul
-/
lemma MulAction.automorphize_smul_left [Group α] [MulAction α β] (f : β -> M)
    (g : Quotient (MulAction.orbitRel α β) -> R) :
    MulAction.automorphize ((g ∘ (@Quotient.mk' _ (_))) • f)
      = g • (MulAction.automorphize f : Quotient (MulAction.orbitRel α β) -> M) := by
  ext x
  induction x using Quotient.inductionOn with | _ b
  simp only [automorphize, Pi.smul_apply', comp_apply]
  set π : β -> Quotient (MulAction.orbitRel α β) := Quotient.mk (MulAction.orbitRel α β)
  have H₁ : forall a : α, π (a • b) = π b := by
    intro a
    apply (@Quotient.eq _ (MulAction.orbitRel α β) (a • b) b).mpr
    use a
  change ∑' a : α, g (π (a • b)) • f (a • b) = g (π b) • ∑' a : α, f (a • b)
  simp_rw [H₁]
  exact tsum_const_smul'' _

section

variable {G : Type*} [Group G] {Γ : Subgroup G}

/-- Given a subgroup `Γ` of a group `G`, and a function `f : G → M`, we "automorphize" `f` to a
  function `G ⧸ Γ → M` by summing over `Γ` orbits, `g ↦ ∑' (γ : Γ), f(γ • g)`. -/
@[to_additive /-- Given a subgroup `Γ` of an additive group `G`, and a function `f : G → M`, we
  automorphize `f` to a function `G ⧸ Γ → M` by summing over `Γ` orbits,
  `g ↦ ∑' (γ : Γ), f(γ • g)`. -/]
/--
Definition of `QuotientGroup.automorphize` / `QuotientGroup.automorphize` 的定义

English:
definition QuotientGroup.automorphize
  signature: (f : G -> M)
  body: MulAction.automorphize f

中文:
定义 QuotientGroup.automorphize
  签名: (f : G -> M)
  定义体: MulAction.automorphize f

Depends on / 依赖: MulAction, MulAction.automorphize, automorphize
-/
noncomputable def QuotientGroup.automorphize (f : G -> M) : G ⧸ Γ -> M := MulAction.automorphize f

/--
lemma `QuotientGroup.automorphize_smul_left` / 引理 `QuotientGroup.automorphize_smul_left`

English:
lemma QuotientGroup.automorphize_smul_left
  given: (f : G -> M) (g : G ⧸ Γ -> R)
  proof: MulAction.automorphize_smul_left f g

中文:
引理 QuotientGroup.automorphize_smul_left
  条件: (f : G -> M) (g : G ⧸ Γ -> R)
  证明: MulAction.automorphize_smul_left f g

Depends on / 依赖: MulAction, MulAction.automorphize_smul_left, automorphize_smul_left
-/
lemma QuotientGroup.automorphize_smul_left (f : G -> M) (g : G ⧸ Γ -> R) :
    (QuotientGroup.automorphize ((g ∘ (@Quotient.mk' _ (_)) : G -> R) • f) : G ⧸ Γ -> M)
      = g • (QuotientGroup.automorphize f : G ⧸ Γ -> M) :=
  MulAction.automorphize_smul_left f g

end

section

variable {G : Type*} [AddGroup G] {Γ : AddSubgroup G}

/--
lemma `QuotientAddGroup.automorphize_smul_left` / 引理 `QuotientAddGroup.automorphize_smul_left`

English:
lemma QuotientAddGroup.automorphize_smul_left
  given: (f : G -> M) (g : G ⧸ Γ -> R)
  proof: AddAction.automorphize_smul_left f g

中文:
引理 QuotientAddGroup.automorphize_smul_left
  条件: (f : G -> M) (g : G ⧸ Γ -> R)
  证明: AddAction.automorphize_smul_left f g

Depends on / 依赖: AddAction, AddAction.automorphize_smul_left, automorphize_smul_left
-/
lemma QuotientAddGroup.automorphize_smul_left (f : G -> M) (g : G ⧸ Γ -> R) :
    QuotientAddGroup.automorphize ((g ∘ (@Quotient.mk' _ (_))) • f)
      = g • (QuotientAddGroup.automorphize f : G ⧸ Γ -> M) :=
  AddAction.automorphize_smul_left f g

end

end automorphize
