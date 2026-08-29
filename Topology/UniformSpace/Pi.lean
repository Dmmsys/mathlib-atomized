/-
Copyright (c) 2019 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
module

public import Mathlib.Topology.UniformSpace.UniformEmbedding

/-!
# Indexed product of uniform spaces
-/

public section


noncomputable section

open scoped Uniformity Topology
open Filter UniformSpace Function Set

universe u

variable {ι ι' β : Type*} (α : ι -> Type u) [U : forall i, UniformSpace (α i)] [UniformSpace β]

/--
Instance `Pi.uniformSpace` / 实例 `Pi.uniformSpace`

English:
instance Pi.uniformSpace
  signature: : UniformSpace (forall i, α i)
  body: UniformSpace.ofCoreEq (⨅ i, UniformSpace.comap (eval i) (U i)).toCore
Pi.topologicalSpace
    Eq.symm toTopologicalSpace_iInf

中文:
实例 Pi.uniformSpace
  签名: : UniformSpace (对任意 i, α i)
  定义体: UniformSpace.ofCoreEq (⨅ i, UniformSpace.comap (eval i) (U i)).toCore
Pi.topologicalSpace
    Eq.symm toTopologicalSpace_iInf

Depends on / 依赖: Eq.symm, Pi.topologicalSpace, UniformSpace, UniformSpace.comap, UniformSpace.ofCoreEq, ofCoreEq, toCore, toTopologicalSpace_iInf, topologicalSpace
-/
instance Pi.uniformSpace : UniformSpace (forall i, α i) :=
  UniformSpace.ofCoreEq (⨅ i, UniformSpace.comap (eval i) (U i)).toCore
Pi.topologicalSpace
    Eq.symm toTopologicalSpace_iInf

/--
lemma `Pi.uniformSpace_eq` / 引理 `Pi.uniformSpace_eq`

English:
lemma Pi.uniformSpace_eq
  proof: by
  ext : 1; rfl

中文:
引理 Pi.uniformSpace_eq
  证明: by
  ext : 1; rfl
-/
lemma Pi.uniformSpace_eq :
    Pi.uniformSpace α = ⨅ i, UniformSpace.comap (eval i) (U i) := by
  ext : 1; rfl

/--
theorem `Pi.uniformity` / 定理 `Pi.uniformity`

English:
theorem Pi.uniformity
  proof: iInf_uniformity

中文:
定理 Pi.uniformity
  证明: iInf_uniformity

Depends on / 依赖: iInf_uniformity
-/
theorem Pi.uniformity :
    𝓤 (forall i, α i) = ⨅ i : ι, (Filter.comap fun a => (a.1 i, a.2 i)) (𝓤 (α i)) :=
  iInf_uniformity

variable {α}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Countable
  signature: ι] [forall i, IsCountablyGenerated (𝓤 (α i))] :
  body: by
  rw [Pi.uniformity]
  infer_instance

中文:
实例 [Countable
  签名: ι] [对任意 i, IsCountablyGenerated (𝓤 (α i))] :
  定义体: by
  rw [Pi.uniformity]
  infer_instance

Depends on / 依赖: Pi.uniformity, infer_instance, uniformity
-/
instance [Countable ι] [forall i, IsCountablyGenerated (𝓤 (α i))] :
    IsCountablyGenerated (𝓤 (forall i, α i)) := by
  rw [Pi.uniformity]
  infer_instance

/--
theorem `uniformContinuous_pi` / 定理 `uniformContinuous_pi`

English:
theorem uniformContinuous_pi
  given: {β : Type*} [UniformSpace β] {f : β -> forall i, α i}
  proof: by
  simp only [UniformContinuous, Pi.uniformity, tendsto_iInf, tendsto_comap_iff, Function.comp_def]

中文:
定理 uniformContinuous_pi
  条件: {β : 类型} [UniformSpace β] {f : β -> 对任意 i, α i}
  证明: by
  simp only [UniformContinuous, Pi.uniformity, tendsto_iInf, tendsto_comap_iff, Function.comp_def]

Depends on / 依赖: Function, Function.comp_def, Pi.uniformity, UniformContinuous, comp_def, tendsto_comap_iff, tendsto_iInf, uniformity
-/
theorem uniformContinuous_pi {β : Type*} [UniformSpace β] {f : β -> forall i, α i} :
    UniformContinuous f ↔ forall i, UniformContinuous fun x => f x i := by
  simp only [UniformContinuous, Pi.uniformity, tendsto_iInf, tendsto_comap_iff, Function.comp_def]

variable (α)

/--
theorem `Pi.uniformContinuous_proj` / 定理 `Pi.uniformContinuous_proj`

English:
theorem Pi.uniformContinuous_proj
  given: (i : ι)
  statement: UniformContinuous fun a : forall i : ι, α i => a i
  proof: uniformContinuous_pi.1 uniformContinuous_id i

中文:
定理 Pi.uniformContinuous_proj
  条件: (i : ι)
  结论: UniformContinuous fun a : 对任意 i : ι, α i => a i
  证明: uniformContinuous_pi.1 uniformContinuous_id i

Depends on / 依赖: uniformContinuous_id, uniformContinuous_pi
-/
theorem Pi.uniformContinuous_proj (i : ι) : UniformContinuous fun a : forall i : ι, α i => a i :=
  uniformContinuous_pi.1 uniformContinuous_id i

/--
theorem `Pi.uniformContinuous_precomp'` / 定理 `Pi.uniformContinuous_precomp'`

English:
theorem Pi.uniformContinuous_precomp'
  given: (φ : ι' -> ι)
  proof: uniformContinuous_pi.mpr fun j => uniformContinuous_proj α (φ j)

中文:
定理 Pi.uniformContinuous_precomp'
  条件: (φ : ι' -> ι)
  证明: uniformContinuous_pi.mpr fun j => uniformContinuous_proj α (φ j)

Depends on / 依赖: uniformContinuous_pi, uniformContinuous_pi.mpr, uniformContinuous_proj
-/
theorem Pi.uniformContinuous_precomp' (φ : ι' -> ι) :
    UniformContinuous (fun (f : (forall i, α i)) (j : ι') => f (φ j)) :=
  uniformContinuous_pi.mpr fun j => uniformContinuous_proj α (φ j)

/--
theorem `Pi.uniformContinuous_precomp` / 定理 `Pi.uniformContinuous_precomp`

English:
theorem Pi.uniformContinuous_precomp
  given: (φ : ι' -> ι)
  proof: Pi.uniformContinuous_precomp' _ φ

中文:
定理 Pi.uniformContinuous_precomp
  条件: (φ : ι' -> ι)
  证明: Pi.uniformContinuous_precomp' _ φ

Depends on / 依赖: Pi.uniformContinuous_precomp, uniformContinuous_precomp
-/
theorem Pi.uniformContinuous_precomp (φ : ι' -> ι) :
    UniformContinuous (· ∘ φ : (ι -> β) -> (ι' -> β)) :=
  Pi.uniformContinuous_precomp' _ φ

/--
theorem `Pi.uniformContinuous_postcomp'` / 定理 `Pi.uniformContinuous_postcomp'`

English:
theorem Pi.uniformContinuous_postcomp'
  statement: {β : ι -> Type*} [forall i, UniformSpace (β i)]
  proof: uniformContinuous_pi.mpr fun i => (hg i).comp uniformContinuous_proj α i

中文:
定理 Pi.uniformContinuous_postcomp'
  结论: {β : ι -> 类型} [对任意 i, UniformSpace (β i)]
  证明: uniformContinuous_pi.mpr fun i => (hg i).comp uniformContinuous_proj α i

Depends on / 依赖: uniformContinuous_pi, uniformContinuous_pi.mpr, uniformContinuous_proj
-/
theorem Pi.uniformContinuous_postcomp' {β : ι -> Type*} [forall i, UniformSpace (β i)]
    {g : forall i, α i -> β i} (hg : forall i, UniformContinuous (g i)) :
    UniformContinuous (fun (f : (forall i, α i)) (i : ι) => g i (f i)) :=
uniformContinuous_pi.mpr fun i => (hg i).comp uniformContinuous_proj α i

/--
theorem `Pi.uniformContinuous_postcomp` / 定理 `Pi.uniformContinuous_postcomp`

English:
theorem Pi.uniformContinuous_postcomp
  statement: {α : Type*} [UniformSpace α] {g : α -> β}
  proof: Pi.uniformContinuous_postcomp' _ fun _ => hg

中文:
定理 Pi.uniformContinuous_postcomp
  结论: {α : 类型} [UniformSpace α] {g : α -> β}
  证明: Pi.uniformContinuous_postcomp' _ fun _ => hg

Depends on / 依赖: Pi.uniformContinuous_postcomp, uniformContinuous_postcomp
-/
theorem Pi.uniformContinuous_postcomp {α : Type*} [UniformSpace α] {g : α -> β}
    (hg : UniformContinuous g) : UniformContinuous (g ∘ · : (ι -> α) -> (ι -> β)) :=
  Pi.uniformContinuous_postcomp' _ fun _ => hg

/--
lemma `Pi.uniformSpace_comap_precomp'` / 引理 `Pi.uniformSpace_comap_precomp'`

English:
lemma Pi.uniformSpace_comap_precomp'
  given: (φ : ι' -> ι)
  proof: by
  simp [Pi.uniformSpace_eq, UniformSpace.comap_iInf, ← UniformSpace.comap_comap, comp_def]

中文:
引理 Pi.uniformSpace_comap_precomp'
  条件: (φ : ι' -> ι)
  证明: by
  simp [Pi.uniformSpace_eq, UniformSpace.comap_iInf, ← UniformSpace.comap_comap, comp_def]

Depends on / 依赖: Pi.uniformSpace_eq, UniformSpace, UniformSpace.comap_comap, UniformSpace.comap_iInf, comap_comap, comap_iInf, comp_def, uniformSpace_eq
-/
lemma Pi.uniformSpace_comap_precomp' (φ : ι' -> ι) :
    UniformSpace.comap (fun g i' => g (φ i')) (Pi.uniformSpace (fun i' => α (φ i'))) =
    ⨅ i', UniformSpace.comap (eval (φ i')) (U (φ i')) := by
  simp [Pi.uniformSpace_eq, UniformSpace.comap_iInf, ← UniformSpace.comap_comap, comp_def]

/--
lemma `Pi.uniformSpace_comap_precomp` / 引理 `Pi.uniformSpace_comap_precomp`

English:
lemma Pi.uniformSpace_comap_precomp
  given: (φ : ι' -> ι)
  proof: uniformSpace_comap_precomp' (fun _ => β) φ

中文:
引理 Pi.uniformSpace_comap_precomp
  条件: (φ : ι' -> ι)
  证明: uniformSpace_comap_precomp' (fun _ => β) φ

Depends on / 依赖: uniformSpace_comap_precomp
-/
lemma Pi.uniformSpace_comap_precomp (φ : ι' -> ι) :
    UniformSpace.comap (· ∘ φ) (Pi.uniformSpace (fun _ => β)) =
    ⨅ i', UniformSpace.comap (eval (φ i')) ‹UniformSpace β› :=
  uniformSpace_comap_precomp' (fun _ => β) φ

/--
lemma `Pi.uniformContinuous_restrict` / 引理 `Pi.uniformContinuous_restrict`

English:
lemma Pi.uniformContinuous_restrict
  given: (S : Set ι)
  proof: Pi.uniformContinuous_precomp' _ ((↑) : S -> ι)

中文:
引理 Pi.uniformContinuous_restrict
  条件: (S : Set ι)
  证明: Pi.uniformContinuous_precomp' _ ((↑) : S -> ι)

Depends on / 依赖: Pi.uniformContinuous_precomp, uniformContinuous_precomp
-/
lemma Pi.uniformContinuous_restrict (S : Set ι) :
    UniformContinuous (S.domRestrict : (forall i : ι, α i) -> (forall i : S, α i)) :=
  Pi.uniformContinuous_precomp' _ ((↑) : S -> ι)

/--
lemma `Pi.uniformSpace_comap_restrict` / 引理 `Pi.uniformSpace_comap_restrict`

English:
lemma Pi.uniformSpace_comap_restrict
  given: (S : Set ι)
  proof: by
  simp +unfoldPartialApp
    [← iInf_subtype'', ← uniformSpace_comap_precomp' _ ((↑) : S -> ι), Set.domRestrict]

中文:
引理 Pi.uniformSpace_comap_restrict
  条件: (S : Set ι)
  证明: by
  simp +unfoldPartialApp
    [← iInf_subtype'', ← uniformSpace_comap_precomp' _ ((↑) : S -> ι), Set.domRestrict]

Depends on / 依赖: Set.domRestrict, domRestrict, iInf_subtype, unfoldPartialApp, uniformSpace_comap_precomp
-/
lemma Pi.uniformSpace_comap_restrict (S : Set ι) :
    UniformSpace.comap (S.domRestrict) (Pi.uniformSpace (fun i : S => α i)) =
    ⨅ i in S, UniformSpace.comap (eval i) (U i) := by
  simp +unfoldPartialApp
    [← iInf_subtype'', ← uniformSpace_comap_precomp' _ ((↑) : S -> ι), Set.domRestrict]

/--
lemma `cauchy_pi_iff` / 引理 `cauchy_pi_iff`

English:
lemma cauchy_pi_iff
  given: [Nonempty ι] {l : Filter (forall i, α i)}
  proof: by
  simp_rw +instances [Pi.uniformSpace_eq, cauchy_iInf_uniformSpace, cauchy_comap_uniformSpace]

中文:
引理 cauchy_pi_iff
  条件: [Nonempty ι] {l : Filter (对任意 i, α i)}
  证明: by
  simp_rw +instances [Pi.uniformSpace_eq, cauchy_iInf_uniformSpace, cauchy_comap_uniformSpace]

Depends on / 依赖: Pi.uniformSpace_eq, cauchy_comap_uniformSpace, cauchy_iInf_uniformSpace, instances, simp_rw, uniformSpace_eq
-/
lemma cauchy_pi_iff [Nonempty ι] {l : Filter (forall i, α i)} :
    Cauchy l ↔ forall i, Cauchy (map (eval i) l) := by
  simp_rw +instances [Pi.uniformSpace_eq, cauchy_iInf_uniformSpace, cauchy_comap_uniformSpace]

/--
lemma `cauchy_pi_iff'` / 引理 `cauchy_pi_iff'`

English:
lemma cauchy_pi_iff'
  given: {l : Filter (forall i, α i)} [l.NeBot]
  proof: by
  simp_rw +instances [Pi.uniformSpace_eq, cauchy_iInf_uniformSpace', cauchy_comap_uniformSpace]

中文:
引理 cauchy_pi_iff'
  条件: {l : Filter (对任意 i, α i)} [l.NeBot]
  证明: by
  simp_rw +instances [Pi.uniformSpace_eq, cauchy_iInf_uniformSpace', cauchy_comap_uniformSpace]

Depends on / 依赖: Pi.uniformSpace_eq, cauchy_comap_uniformSpace, cauchy_iInf_uniformSpace, instances, simp_rw, uniformSpace_eq
-/
lemma cauchy_pi_iff' {l : Filter (forall i, α i)} [l.NeBot] :
    Cauchy l ↔ forall i, Cauchy (map (eval i) l) := by
  simp_rw +instances [Pi.uniformSpace_eq, cauchy_iInf_uniformSpace', cauchy_comap_uniformSpace]

/--
lemma `Cauchy.pi` / 引理 `Cauchy.pi`

English:
lemma Cauchy.pi
  given: [Nonempty ι] {l : forall i, Filter (α i)} (hl : forall i, Cauchy (l i))
  proof: by
  have := fun i => (hl i).1
  simpa [cauchy_pi_iff]

中文:
引理 Cauchy.pi
  条件: [Nonempty ι] {l : 对任意 i, Filter (α i)} (hl : 对任意 i, Cauchy (l i))
  证明: by
  have := fun i => (hl i).1
  simpa [cauchy_pi_iff]

Depends on / 依赖: cauchy_pi_iff
-/
lemma Cauchy.pi [Nonempty ι] {l : forall i, Filter (α i)} (hl : forall i, Cauchy (l i)) :
    Cauchy (Filter.pi l) := by
  have := fun i => (hl i).1
  simpa [cauchy_pi_iff]

/--
Instance `Pi.complete` / 实例 `Pi.complete`

English:
instance Pi.complete
  signature: [forall i, CompleteSpace (α i)]
  body: by
    have := hf.1
    simp_rw [cauchy_pi_iff', cauchy_iff_exists_le_nhds] at hf
    choose x hx using hf
    use x
    rwa [nhds_pi, le_pi]

中文:
实例 Pi.complete
  签名: [对任意 i, CompleteSpace (α i)]
  定义体: by
    have := hf.1
    simp_rw [cauchy_pi_iff', cauchy_iff_exists_le_nhds] at hf
    choose x hx using hf
    use x
    rwa [nhds_pi, le_pi]

Depends on / 依赖: cauchy_iff_exists_le_nhds, cauchy_pi_iff, le_pi, nhds_pi, simp_rw
-/
instance Pi.complete [forall i, CompleteSpace (α i)] : CompleteSpace (forall i, α i) where
  complete {f} hf := by
    have := hf.1
    simp_rw [cauchy_pi_iff', cauchy_iff_exists_le_nhds] at hf
    choose x hx using hf
    use x
    rwa [nhds_pi, le_pi]

/--
lemma `Pi.uniformSpace_comap_restrict_sUnion` / 引理 `Pi.uniformSpace_comap_restrict_sUnion`

English:
lemma Pi.uniformSpace_comap_restrict_sUnion
  given: (𝔖 : Set (Set ι))
  proof: by
  simp_rw [Pi.uniformSpace_comap_restrict α, iInf_sUnion]

中文:
引理 Pi.uniformSpace_comap_restrict_sUnion
  条件: (𝔖 : Set (Set ι))
  证明: by
  simp_rw [Pi.uniformSpace_comap_restrict α, iInf_sUnion]

Depends on / 依赖: Pi.uniformSpace_comap_restrict, iInf_sUnion, simp_rw, uniformSpace_comap_restrict
-/
lemma Pi.uniformSpace_comap_restrict_sUnion (𝔖 : Set (Set ι)) :
    UniformSpace.comap (⋃₀ 𝔖).domRestrict (Pi.uniformSpace (fun i : (⋃₀ 𝔖) => α i)) =
    ⨅ S in 𝔖, UniformSpace.comap S.domRestrict (Pi.uniformSpace (fun i : S => α i)) := by
  simp_rw [Pi.uniformSpace_comap_restrict α, iInf_sUnion]

/--
theorem `CompleteSpace.iInf` / 定理 `CompleteSpace.iInf`

English:
theorem CompleteSpace.iInf
  statement: {ι X : Type*} {u : ι -> UniformSpace X}
  proof: by
  -- We can assume `X` is nonempty.
  nontriviality X
  rcases ht with ⟨t, ht, hut⟩
  -- The diagonal map `(X, ⨅ i, u i) → ∀ i, (X, u i)` is a uniform embedding.
  have : @IsUniformInducing X (ι -> X) (⨅ i, u i) (Pi.uniformSpace (U := u)) (const ι) := by
    simp_rw [isUniformInducing_iff, iInf_u

中文:
定理 CompleteSpace.iInf
  结论: {ι X : 类型} {u : ι -> UniformSpace X}
  证明: by
  -- We can assume `X` is nonempty.
  nontriviality X
  rcases ht with ⟨t, ht, hut⟩
  -- The diagonal map `(X, ⨅ i, u i) → ∀ i, (X, u i)` is a uniform embedding.
  have : @IsUniformInducing X (ι -> X) (⨅ i, u i) (Pi.uniformSpace (U := u)) (const ι) := by
    simp_rw [isUniformInducing_iff, iInf_u
-/
protected theorem CompleteSpace.iInf {ι X : Type*} {u : ι -> UniformSpace X}
    (hu : forall i, @CompleteSpace X (u i))
    (ht : exists t, @T2Space X t ∧ forall i, (u i).toTopologicalSpace <= t) :
    @CompleteSpace X (⨅ i, u i) := by
  -- We can assume `X` is nonempty.
  nontriviality X
  rcases ht with ⟨t, ht, hut⟩
  -- The diagonal map `(X, ⨅ i, u i) → ∀ i, (X, u i)` is a uniform embedding.
  have : @IsUniformInducing X (ι -> X) (⨅ i, u i) (Pi.uniformSpace (U := u)) (const ι) := by
    simp_rw [isUniformInducing_iff, iInf_uniformity, Pi.uniformity, Filter.comap_iInf,
      Filter.comap_comap, comp_def, const, Prod.eta, comap_id']
  -- Hence, it suffices to show that its range, the diagonal, is closed in `Π i, (X, u i)`.
  simp_rw [@completeSpace_iff_isComplete_range _ _ (_) (_) _ this, range_const_eq_diagonal,
    ofPred_forall]
  -- The separation of `t` ensures that this is the case in `Π i, (X, t)`, hence the result
  -- since the topology associated to each `u i` is finer than `t`.
  have : Pi.topologicalSpace (t₂ := fun i => (u i).toTopologicalSpace) <=
         Pi.topologicalSpace (t₂ := fun _ => t) :=
iInf_mono fun i => induced_mono hut i
refine IsClosed.isComplete .mono ?_ this
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    isClosed_eq (continuous_apply _) (continuous_apply _)
