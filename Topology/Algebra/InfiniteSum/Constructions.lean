/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Order.Filter.AtTopBot.Finset
public import Mathlib.Topology.Algebra.InfiniteSum.Group
public import Mathlib.Topology.Algebra.Star

/-!
# Topological sums and functorial constructions

Lemmas on the interaction of `tprod`, `tsum`, `HasProd`, `HasSum` etc. with products, Sigma and Pi
types, `MulOpposite`, etc.

-/

public section

noncomputable section

open Filter Finset Function

open scoped Topology

variable {α β γ : Type*} {L : SummationFilter β}


/-! ## Product, Sigma and Pi types -/

section ProdDomain

variable [CommMonoid α] [TopologicalSpace α]

@[to_additive]
/--
theorem `hasProd_pi_single` / 定理 `hasProd_pi_single`

English:
theorem hasProd_pi_single
  given: [DecidableEq β] (b : β) (a : α)
  statement: HasProd (Pi.mulSingle b a) a
  proof: by
  convert! hasProd_ite_eq (L := .unconditional β) b a
  simp [Pi.mulSingle_apply]

@[to_additive (attr := simp)]

中文:
定理 hasProd_pi_single
  条件: [DecidableEq β] (b : β) (a : α)
  结论: HasProd (Pi.mulSingle b a) a
  证明: by
  convert! hasProd_ite_eq (L := .unconditional β) b a
  simp [Pi.mulSingle_apply]

@[to_additive (attr := simp)]

Depends on / 依赖: Pi.mulSingle_apply, convert, hasProd_ite_eq, mulSingle_apply, unconditional
-/
theorem hasProd_pi_single [DecidableEq β] (b : β) (a : α) : HasProd (Pi.mulSingle b a) a := by
  convert! hasProd_ite_eq (L := .unconditional β) b a
  simp [Pi.mulSingle_apply]

@[to_additive (attr := simp)]
/--
theorem `tprod_pi_single` / 定理 `tprod_pi_single`

English:
theorem tprod_pi_single
  given: [DecidableEq β] (b : β) (a : α)
  statement: ∏' b', Pi.mulSingle b a b' = a
  proof: by
  rw [tprod_eq_mulSingle b]
  · simp
  · intro b' hb'; simp [hb']

@[to_additive tsum_setProd_singleton_left]

中文:
定理 tprod_pi_single
  条件: [DecidableEq β] (b : β) (a : α)
  结论: ∏' b', Pi.mulSingle b a b' = a
  证明: by
  rw [tprod_eq_mulSingle b]
  · simp
  · intro b' hb'; simp [hb']

@[to_additive tsum_setProd_singleton_left]

Depends on / 依赖: tprod_eq_mulSingle
-/
theorem tprod_pi_single [DecidableEq β] (b : β) (a : α) : ∏' b', Pi.mulSingle b a b' = a := by
  rw [tprod_eq_mulSingle b]
  · simp
  · intro b' hb'; simp [hb']

@[to_additive tsum_setProd_singleton_left]
/--
lemma `tprod_setProd_singleton_left` / 引理 `tprod_setProd_singleton_left`

English:
lemma tprod_setProd_singleton_left
  given: (b : β) (t : Set γ) (f : β × γ -> α)
  proof: by
  rw [tprod_congr_set_coe _ Set.singleton_prod]; rw [tprod_image _ (Prod.mk_right_injective b).injOn]

@[to_additive tsum_setProd_singleton_right]

中文:
引理 tprod_setProd_singleton_left
  条件: (b : β) (t : Set γ) (f : β × γ -> α)
  证明: by
  rw [tprod_congr_set_coe _ Set.singleton_prod]; rw [tprod_image _ (Prod.mk_right_injective b).injOn]

@[to_additive tsum_setProd_singleton_right]

Depends on / 依赖: Prod.mk_right_injective, Set.singleton_prod, mk_right_injective, singleton_prod, tprod_congr_set_coe, tprod_image
-/
lemma tprod_setProd_singleton_left (b : β) (t : Set γ) (f : β × γ -> α) :
    (∏' x : {b} ×ˢ t, f x) = ∏' c : t, f (b, c) := by
  rw [tprod_congr_set_coe _ Set.singleton_prod]; rw [tprod_image _ (Prod.mk_right_injective b).injOn]

@[to_additive tsum_setProd_singleton_right]
/--
lemma `tprod_setProd_singleton_right` / 引理 `tprod_setProd_singleton_right`

English:
lemma tprod_setProd_singleton_right
  given: (s : Set β) (c : γ) (f : β × γ -> α)
  proof: by
  rw [tprod_congr_set_coe _ Set.prod_singleton]; rw [tprod_image _ (Prod.mk_left_injective c).injOn]

@[to_additive Summable.prod_symm]

中文:
引理 tprod_setProd_singleton_right
  条件: (s : Set β) (c : γ) (f : β × γ -> α)
  证明: by
  rw [tprod_congr_set_coe _ Set.prod_singleton]; rw [tprod_image _ (Prod.mk_left_injective c).injOn]

@[to_additive Summable.prod_symm]

Depends on / 依赖: Prod.mk_left_injective, Set.prod_singleton, mk_left_injective, prod_singleton, tprod_congr_set_coe, tprod_image
-/
lemma tprod_setProd_singleton_right (s : Set β) (c : γ) (f : β × γ -> α) :
    (∏' x : s ×ˢ {c}, f x) = ∏' b : s, f (b, c) := by
  rw [tprod_congr_set_coe _ Set.prod_singleton]; rw [tprod_image _ (Prod.mk_left_injective c).injOn]

@[to_additive Summable.prod_symm]
/--
theorem `Multipliable.prod_symm` / 定理 `Multipliable.prod_symm`

English:
theorem Multipliable.prod_symm
  given: {f : β × γ -> α} (hf : Multipliable f)
  proof: (Equiv.prodComm γ β).multipliable_iff.2 hf

中文:
定理 Multipliable.prod_symm
  条件: {f : β × γ -> α} (hf : Multipliable f)
  证明: (Equiv.prodComm γ β).multipliable_iff.2 hf

Depends on / 依赖: Equiv.prodComm, multipliable_iff, prodComm
-/
theorem Multipliable.prod_symm {f : β × γ -> α} (hf : Multipliable f) :
    Multipliable fun p : γ × β => f p.swap :=
  (Equiv.prodComm γ β).multipliable_iff.2 hf

end ProdDomain

section ProdCodomain

variable [CommMonoid α] [TopologicalSpace α] [CommMonoid γ] [TopologicalSpace γ]

@[to_additive HasSum.prodMk]
/--
theorem `HasProd.prodMk` / 定理 `HasProd.prodMk`

English:
theorem HasProd.prodMk
  statement: {f : β -> α} {g : β -> γ} {a : α} {b : γ} (hf : HasProd f a L)
  proof: by
  simp [HasProd, ← prod_mk_prod, Filter.Tendsto.prodMk_nhds hf hg]

中文:
定理 HasProd.prodMk
  结论: {f : β -> α} {g : β -> γ} {a : α} {b : γ} (hf : HasProd f a L)
  证明: by
  simp [HasProd, ← prod_mk_prod, Filter.Tendsto.prodMk_nhds hf hg]

Depends on / 依赖: Filter, Filter.Tendsto.prodMk_nhds, HasProd, Tendsto, prodMk_nhds, prod_mk_prod
-/
theorem HasProd.prodMk {f : β -> α} {g : β -> γ} {a : α} {b : γ} (hf : HasProd f a L)
    (hg : HasProd g b L) : HasProd (fun x => (⟨f x, g x⟩ : α × γ)) ⟨a, b⟩ L := by
  simp [HasProd, ← prod_mk_prod, Filter.Tendsto.prodMk_nhds hf hg]

end ProdCodomain

section ContinuousMul

variable [CommMonoid α] [TopologicalSpace α] [ContinuousMul α]

section Sum

@[to_additive]
/--
lemma `HasProd.sum` / 引理 `HasProd.sum`

English:
lemma HasProd.sum
  statement: {α β M : Type*} [CommMonoid M] [TopologicalSpace M] [ContinuousMul M]
  proof: by
  have : Tendsto ((∏ b in ·, f b) ∘ sumEquiv.symm) (atTop.map sumEquiv) (nhds (a * b)) := by
    rw [Finset.sumEquiv.map_atTop]; rw [← prod_atTop_atTop_eq]
    convert! (tendsto_mul.comp (nhds_prod_eq (x := a) (y := b) ▸ Tendsto.prodMap h₁ h₂))
    ext s
    simp
  simpa [Tendsto, ← Filter.map_ma

中文:
引理 HasProd.sum
  结论: {α β M : 类型} [CommMonoid M] [TopologicalSpace M] [ContinuousMul M]
  证明: by
  have : Tendsto ((∏ b in ·, f b) ∘ sumEquiv.symm) (atTop.map sumEquiv) (nhds (a * b)) := by
    rw [Finset.sumEquiv.map_atTop]; rw [← prod_atTop_atTop_eq]
    convert! (tendsto_mul.comp (nhds_prod_eq (x := a) (y := b) ▸ Tendsto.prodMap h₁ h₂))
    ext s
    simp
  simpa [Tendsto, ← Filter.map_ma

Depends on / 依赖: Filter, Filter.map_map, Finset, Finset.sumEquiv.map_atTop, Tendsto, Tendsto.prodMap, atTop.map, convert, map_atTop, map_map, nhds_prod_eq, prodMap, prod_atTop_atTop_eq, sumEquiv, sumEquiv.symm, tendsto_mul, tendsto_mul.comp
-/
lemma HasProd.sum {α β M : Type*} [CommMonoid M] [TopologicalSpace M] [ContinuousMul M]
    {f : α oplus β -> M} {a b : M}
    (h₁ : HasProd (f ∘ Sum.inl) a) (h₂ : HasProd (f ∘ Sum.inr) b) : HasProd f (a * b) := by
  have : Tendsto ((∏ b in ·, f b) ∘ sumEquiv.symm) (atTop.map sumEquiv) (nhds (a * b)) := by
    rw [Finset.sumEquiv.map_atTop]; rw [← prod_atTop_atTop_eq]
    convert! (tendsto_mul.comp (nhds_prod_eq (x := a) (y := b) ▸ Tendsto.prodMap h₁ h₂))
    ext s
    simp
  simpa [Tendsto, ← Filter.map_map] using! this

@[to_additive /-- For the statement that `tsum` commutes with `Finset.sum`,
  see `Summable.tsum_finsetSum`. -/]
/--
lemma `Multipliable.tprod_sum` / 引理 `Multipliable.tprod_sum`

English:
lemma Multipliable.tprod_sum
  statement: {α β M : Type*} [CommMonoid M] [TopologicalSpace M]
  proof: (h₁.hasProd.sum h₂.hasProd).tprod_eq

@[to_additive]

中文:
引理 Multipliable.tprod_sum
  结论: {α β M : 类型} [CommMonoid M] [TopologicalSpace M]
  证明: (h₁.hasProd.sum h₂.hasProd).tprod_eq

@[to_additive]
-/
protected lemma Multipliable.tprod_sum {α β M : Type*} [CommMonoid M] [TopologicalSpace M]
    [ContinuousMul M] [T2Space M] {f : α oplus β -> M} (h₁ : Multipliable (f ∘ .inl))
    (h₂ : Multipliable (f ∘ .inr)) : ∏' i, f i = (∏' i, f (.inl i)) * (∏' i, f (.inr i)) :=
  (h₁.hasProd.sum h₂.hasProd).tprod_eq

@[to_additive]
/--
lemma `Multipliable.sum` / 引理 `Multipliable.sum`

English:
lemma Multipliable.sum
  statement: {α β M : Type*} [CommMonoid M] [TopologicalSpace M] [ContinuousMul M]
  proof: ⟨_, .sum h₁.hasProd h₂.hasProd⟩

中文:
引理 Multipliable.sum
  结论: {α β M : 类型} [CommMonoid M] [TopologicalSpace M] [ContinuousMul M]
  证明: ⟨_, .sum h₁.hasProd h₂.hasProd⟩

Depends on / 依赖: hasProd
-/
lemma Multipliable.sum {α β M : Type*} [CommMonoid M] [TopologicalSpace M] [ContinuousMul M]
    (f : α oplus β -> M) (h₁ : Multipliable (f ∘ Sum.inl)) (h₂ : Multipliable (f ∘ Sum.inr)) :
    Multipliable f :=
  ⟨_, .sum h₁.hasProd h₂.hasProd⟩

end Sum

section RegularSpace

variable [RegularSpace α]

@[to_additive]
/--
theorem `HasProd.sigma` / 定理 `HasProd.sigma`

English:
theorem HasProd.sigma
  statement: {γ : β -> Type*} {f : (Σ b : β, γ b) -> α} {g : β -> α} {a : α}
  proof: by
  classical
  refine (atTop_basis.tendsto_iff (closed_nhds_basis a)).mpr ?_
  rintro s ⟨hs, hsc⟩
  rcases mem_atTop_sets.mp (ha hs) with ⟨u, hu⟩
  use u.image Sigma.fst, trivial
  intro bs hbs
  simp only [Set.mem_preimage] at hu
  have : Tendsto (fun t : Finset (Σ b, γ b) => ∏ p in t with p.1 in

中文:
定理 HasProd.sigma
  结论: {γ : β -> 类型} {f : (Σ b : β, γ b) -> α} {g : β -> α} {a : α}
  证明: by
  classical
  refine (atTop_basis.tendsto_iff (closed_nhds_basis a)).mpr ?_
  rintro s ⟨hs, hsc⟩
  rcases mem_atTop_sets.mp (ha hs) with ⟨u, hu⟩
  use u.image Sigma.fst, trivial
  intro bs hbs
  simp only [Set.mem_preimage] at hu
  have : Tendsto (fun t : Finset (Σ b, γ b) => ∏ p in t with p.1 in

Depends on / 依赖: Finset, Set.mem_preimage, Sigma.fst, Sigma.mk, Tendsto, atTop_basis, atTop_basis.tendsto_iff, classical, closed_nhds_basis, mem_atTop_sets, mem_atTop_sets.mp, mem_preimage, preimage, prod_sigma, sigma_preimage_mk, tendsto_finsetProd, tendsto_iff, u.image
-/
theorem HasProd.sigma {γ : β -> Type*} {f : (Σ b : β, γ b) -> α} {g : β -> α} {a : α}
    (ha : HasProd f a) (hf : forall b, HasProd (fun c => f ⟨b, c⟩) (g b)) : HasProd g a := by
  classical
  refine (atTop_basis.tendsto_iff (closed_nhds_basis a)).mpr ?_
  rintro s ⟨hs, hsc⟩
  rcases mem_atTop_sets.mp (ha hs) with ⟨u, hu⟩
  use u.image Sigma.fst, trivial
  intro bs hbs
  simp only [Set.mem_preimage] at hu
  have : Tendsto (fun t : Finset (Σ b, γ b) => ∏ p in t with p.1 in bs, f p) atTop
      (𝓝 <| ∏ b in bs, g b) := by
    simp only [← sigma_preimage_mk, prod_sigma]
    refine tendsto_finsetProd _ fun b _ => ?_
    change
      Tendsto (fun t => (fun t => ∏ s in t, f ⟨b, s⟩) (preimage t (Sigma.mk b) _)) atTop (𝓝 (g b))
    exact (hf b).comp (tendsto_finset_preimage_atTop_atTop (sigma_mk_injective))
  refine hsc.mem_of_tendsto this (eventually_atTop.2 ⟨u, fun t ht => hu _ fun x hx => ?_⟩)
exact mem_filter.2 ⟨ht hx, hbs mem_image_of_mem _ hx⟩

/-- If a function `f` on `β × γ` has product `a` and for each `b` the restriction of `f` to
`{b} × γ` has product `g b`, then the function `g` has product `a`. -/
@[to_additive HasSum.prod_fiberwise /-- If a series `f` on `β × γ` has sum `a` and for each `b` the
restriction of `f` to `{b} × γ` has sum `g b`, then the series `g` has sum `a`. -/]
/--
theorem `HasProd.prod_fiberwise` / 定理 `HasProd.prod_fiberwise`

English:
theorem HasProd.prod_fiberwise
  statement: {f : β × γ -> α} {g : β -> α} {a : α} (ha : HasProd f a)
  proof: HasProd.sigma ((Equiv.sigmaEquivProd β γ).hasProd_iff.2 ha) hf

@[to_additive]

中文:
定理 HasProd.prod_fiberwise
  结论: {f : β × γ -> α} {g : β -> α} {a : α} (ha : HasProd f a)
  证明: HasProd.sigma ((Equiv.sigmaEquivProd β γ).hasProd_iff.2 ha) hf

@[to_additive]

Depends on / 依赖: Equiv.sigmaEquivProd, HasProd, HasProd.sigma, hasProd_iff, sigmaEquivProd
-/
theorem HasProd.prod_fiberwise {f : β × γ -> α} {g : β -> α} {a : α} (ha : HasProd f a)
    (hf : forall b, HasProd (fun c => f (b, c)) (g b)) : HasProd g a :=
  HasProd.sigma ((Equiv.sigmaEquivProd β γ).hasProd_iff.2 ha) hf

@[to_additive]
/--
theorem `Multipliable.sigma'` / 定理 `Multipliable.sigma'`

English:
theorem Multipliable.sigma'
  statement: {γ : β -> Type*} {f : (Σ b : β, γ b) -> α} (ha : Multipliable f)
  proof: (ha.hasProd.sigma fun b => (hf b).hasProd).multipliable

中文:
定理 Multipliable.sigma'
  结论: {γ : β -> 类型} {f : (Σ b : β, γ b) -> α} (ha : Multipliable f)
  证明: (ha.hasProd.sigma fun b => (hf b).hasProd).multipliable

Depends on / 依赖: ha.hasProd.sigma, hasProd, multipliable
-/
theorem Multipliable.sigma' {γ : β -> Type*} {f : (Σ b : β, γ b) -> α} (ha : Multipliable f)
    (hf : forall b, Multipliable fun c => f ⟨b, c⟩) : Multipliable fun b => ∏' c, f ⟨b, c⟩ :=
  (ha.hasProd.sigma fun b => (hf b).hasProd).multipliable

end RegularSpace

section T3Space

variable [T3Space α]

@[to_additive]
/--
theorem `HasProd.sigma_of_hasProd` / 定理 `HasProd.sigma_of_hasProd`

English:
theorem HasProd.sigma_of_hasProd
  statement: {γ : β -> Type*} {f : (Σ b : β, γ b) -> α} {g : β -> α}
  proof: by simpa [(hf'.hasProd.sigma hf).unique ha] using hf'.hasProd

@[to_additive]

中文:
定理 HasProd.sigma_of_hasProd
  结论: {γ : β -> 类型} {f : (Σ b : β, γ b) -> α} {g : β -> α}
  证明: by simpa [(hf'.hasProd.sigma hf).unique ha] using hf'.hasProd

@[to_additive]

Depends on / 依赖: hasProd, hasProd.sigma, unique
-/
theorem HasProd.sigma_of_hasProd {γ : β -> Type*} {f : (Σ b : β, γ b) -> α} {g : β -> α}
    {a : α} (ha : HasProd g a) (hf : forall b, HasProd (fun c => f ⟨b, c⟩) (g b)) (hf' : Multipliable f) :
    HasProd f a := by simpa [(hf'.hasProd.sigma hf).unique ha] using hf'.hasProd

@[to_additive]
/--
theorem `Multipliable.tprod_sigma'` / 定理 `Multipliable.tprod_sigma'`

English:
theorem Multipliable.tprod_sigma'
  statement: {γ : β -> Type*} {f : (Σ b : β, γ b) -> α}
  proof: (h₂.hasProd.sigma fun b => (h₁ b).hasProd).tprod_eq.symm

@[to_additive Summable.tsum_prod']

中文:
定理 Multipliable.tprod_sigma'
  结论: {γ : β -> 类型} {f : (Σ b : β, γ b) -> α}
  证明: (h₂.hasProd.sigma fun b => (h₁ b).hasProd).tprod_eq.symm

@[to_additive Summable.tsum_prod']
-/
protected theorem Multipliable.tprod_sigma' {γ : β -> Type*} {f : (Σ b : β, γ b) -> α}
    (h₁ : forall b, Multipliable fun c => f ⟨b, c⟩) (h₂ : Multipliable f) :
    ∏' p, f p = ∏' (b) (c), f ⟨b, c⟩ :=
  (h₂.hasProd.sigma fun b => (h₁ b).hasProd).tprod_eq.symm

@[to_additive Summable.tsum_prod']
/--
theorem `Multipliable.tprod_prod'` / 定理 `Multipliable.tprod_prod'`

English:
theorem Multipliable.tprod_prod'
  statement: {f : β × γ -> α} (h : Multipliable f)
  proof: (h.hasProd.prod_fiberwise fun b => (h₁ b).hasProd).tprod_eq.symm

@[to_additive Summable.tsum_prod_uncurry]

中文:
定理 Multipliable.tprod_prod'
  结论: {f : β × γ -> α} (h : Multipliable f)
  证明: (h.hasProd.prod_fiberwise fun b => (h₁ b).hasProd).tprod_eq.symm

@[to_additive Summable.tsum_prod_uncurry]
-/
protected theorem Multipliable.tprod_prod' {f : β × γ -> α} (h : Multipliable f)
    (h₁ : forall b, Multipliable fun c => f (b, c)) :
    ∏' p, f p = ∏' (b) (c), f (b, c) :=
  (h.hasProd.prod_fiberwise fun b => (h₁ b).hasProd).tprod_eq.symm

@[to_additive Summable.tsum_prod_uncurry]
/--
theorem `Multipliable.tprod_prod_uncurry` / 定理 `Multipliable.tprod_prod_uncurry`

English:
theorem Multipliable.tprod_prod_uncurry
  statement: {f : β -> γ -> α}
  proof: (h.hasProd.prod_fiberwise fun b => (h₁ b).hasProd).tprod_eq.symm

@[to_additive]

中文:
定理 Multipliable.tprod_prod_uncurry
  结论: {f : β -> γ -> α}
  证明: (h.hasProd.prod_fiberwise fun b => (h₁ b).hasProd).tprod_eq.symm

@[to_additive]
-/
protected theorem Multipliable.tprod_prod_uncurry {f : β -> γ -> α}
    (h : Multipliable (Function.uncurry f)) (h₁ : forall b, Multipliable fun c => f b c) :
    ∏' p : β × γ, uncurry f p = ∏' (b) (c), f b c :=
  (h.hasProd.prod_fiberwise fun b => (h₁ b).hasProd).tprod_eq.symm

@[to_additive]
/--
theorem `Multipliable.tprod_comm'` / 定理 `Multipliable.tprod_comm'`

English:
theorem Multipliable.tprod_comm'
  statement: {f : β -> γ -> α} (h : Multipliable (Function.uncurry f))
  proof: by
  rw [← h.tprod_prod_uncurry h₁]; rw [← h.prod_symm.tprod_prod_uncurry h₂]; rw [← (Equiv.prodComm γ β).tprod_eq (uncurry f)]
  rfl

中文:
定理 Multipliable.tprod_comm'
  结论: {f : β -> γ -> α} (h : Multipliable (Function.uncurry f))
  证明: by
  rw [← h.tprod_prod_uncurry h₁]; rw [← h.prod_symm.tprod_prod_uncurry h₂]; rw [← (Equiv.prodComm γ β).tprod_eq (uncurry f)]
  rfl
-/
protected theorem Multipliable.tprod_comm' {f : β -> γ -> α} (h : Multipliable (Function.uncurry f))
    (h₁ : forall b, Multipliable (f b)) (h₂ : forall c, Multipliable fun b => f b c) :
    ∏' (c) (b), f b c = ∏' (b) (c), f b c := by
  rw [← h.tprod_prod_uncurry h₁]; rw [← h.prod_symm.tprod_prod_uncurry h₂]; rw [← (Equiv.prodComm γ β).tprod_eq (uncurry f)]
  rfl

end T3Space

end ContinuousMul

section CompleteSpace

variable [CommGroup α] [UniformSpace α] [IsUniformGroup α]

@[to_additive]
/--
theorem `HasProd.of_sigma` / 定理 `HasProd.of_sigma`

English:
theorem HasProd.of_sigma
  statement: {γ : β -> Type*} {f : (Σ b : β, γ b) -> α} {g : β -> α} {a : α}
  proof: by
  classical
  apply le_nhds_of_cauchy_adhp h
  simp only [← mapClusterPt_def, mapClusterPt_iff_frequently, frequently_atTop]
  intro u hu s
  rcases mem_nhds_iff.1 hu with ⟨v, vu, v_open, hv⟩
  obtain ⟨t0, st0, ht0⟩ : exists t0, ∏ i in t0, g i in v ∧ s.image Sigma.fst subseteq t0 := by
    have A

中文:
定理 HasProd.of_sigma
  结论: {γ : β -> 类型} {f : (Σ b : β, γ b) -> α} {g : β -> α} {a : α}
  证明: by
  classical
  apply le_nhds_of_cauchy_adhp h
  simp only [← mapClusterPt_def, mapClusterPt_iff_frequently, frequently_atTop]
  intro u hu s
  rcases mem_nhds_iff.1 hu with ⟨v, vu, v_open, hv⟩
  obtain ⟨t0, st0, ht0⟩ : exists t0, ∏ i in t0, g i in v ∧ s.image Sigma.fst subseteq t0 := by
    have A

Depends on / 依赖: A.and, Filter, Finset, Ici_mem_atTop, Sigma.fst, Tendsto, classical, frequently_atTop, le_nhds_of_cauchy_adhp, mapClusterPt_def, mapClusterPt_iff_frequently, mem_nhds, mem_nhds_iff, s.image, subseteq, v_open, v_open.mem_nhds
-/
theorem HasProd.of_sigma {γ : β -> Type*} {f : (Σ b : β, γ b) -> α} {g : β -> α} {a : α}
    (hf : forall b, HasProd (fun c => f ⟨b, c⟩) (g b)) (hg : HasProd g a)
    (h : CauchySeq (fun (s : Finset (Σ b : β, γ b)) => ∏ i in s, f i)) :
    HasProd f a := by
  classical
  apply le_nhds_of_cauchy_adhp h
  simp only [← mapClusterPt_def, mapClusterPt_iff_frequently, frequently_atTop]
  intro u hu s
  rcases mem_nhds_iff.1 hu with ⟨v, vu, v_open, hv⟩
  obtain ⟨t0, st0, ht0⟩ : exists t0, ∏ i in t0, g i in v ∧ s.image Sigma.fst subseteq t0 := by
    have A : forallᶠ t0 in (atTop : Filter (Finset β)), ∏ i in t0, g i in v := hg (v_open.mem_nhds hv)
    exact (A.and (Ici_mem_atTop _)).exists
  have L : Tendsto (fun t : Finset (Σ b, γ b) => ∏ p in t with p.1 in t0, f p) atTop
      (𝓝 <| ∏ b in t0, g b) := by
    simp only [← sigma_preimage_mk, prod_sigma]
    refine tendsto_finsetProd _ fun b _ => ?_
    change
      Tendsto (fun t => (fun t => ∏ s in t, f ⟨b, s⟩) (preimage t (Sigma.mk b) _)) atTop (𝓝 (g b))
    exact (hf b).comp (tendsto_finset_preimage_atTop_atTop (sigma_mk_injective))
  have : exists t, ∏ p in t with p.1 in t0, f p in v ∧ s subseteq t :=
    ((Tendsto.eventually_mem L (v_open.mem_nhds st0)).and (Ici_mem_atTop _)).exists
  obtain ⟨t, tv, st⟩ := this
  refine ⟨{p in t | p.1 in t0}, fun x hx => ?_, vu tv⟩
  simpa only [mem_filter, st hx, true_and] using ht0 (mem_image_of_mem Sigma.fst hx)

variable [CompleteSpace α]

@[to_additive]
/--
theorem `Multipliable.sigma_factor` / 定理 `Multipliable.sigma_factor`

English:
theorem Multipliable.sigma_factor
  statement: {γ : β -> Type*} {f : (Σ b : β, γ b) -> α}
  proof: ha.comp_injective sigma_mk_injective

@[to_additive]

中文:
定理 Multipliable.sigma_factor
  结论: {γ : β -> 类型} {f : (Σ b : β, γ b) -> α}
  证明: ha.comp_injective sigma_mk_injective

@[to_additive]

Depends on / 依赖: comp_injective, ha.comp_injective, sigma_mk_injective
-/
theorem Multipliable.sigma_factor {γ : β -> Type*} {f : (Σ b : β, γ b) -> α}
    (ha : Multipliable f) (b : β) :
    Multipliable fun c => f ⟨b, c⟩ :=
  ha.comp_injective sigma_mk_injective

@[to_additive]
/--
theorem `Multipliable.sigma` / 定理 `Multipliable.sigma`

English:
theorem Multipliable.sigma
  given: {γ : β -> Type*} {f : (Σ b : β, γ b) -> α} (ha : Multipliable f)
  proof: ha.sigma' fun b => ha.sigma_factor b

@[to_additive Summable.prod_factor]

中文:
定理 Multipliable.sigma
  条件: {γ : β -> 类型} {f : (Σ b : β, γ b) -> α} (ha : Multipliable f)
  证明: ha.sigma' fun b => ha.sigma_factor b

@[to_additive Summable.prod_factor]

Depends on / 依赖: ha.sigma, ha.sigma_factor, sigma_factor
-/
theorem Multipliable.sigma {γ : β -> Type*} {f : (Σ b : β, γ b) -> α} (ha : Multipliable f) :
    Multipliable fun b => ∏' c, f ⟨b, c⟩ :=
  ha.sigma' fun b => ha.sigma_factor b

@[to_additive Summable.prod_factor]
/--
theorem `Multipliable.prod_factor` / 定理 `Multipliable.prod_factor`

English:
theorem Multipliable.prod_factor
  given: {f : β × γ -> α} (h : Multipliable f) (b : β)
  proof: h.comp_injective fun _ _ h => (Prod.ext_iff.1 h).2

@[to_additive Summable.prod]

中文:
定理 Multipliable.prod_factor
  条件: {f : β × γ -> α} (h : Multipliable f) (b : β)
  证明: h.comp_injective fun _ _ h => (Prod.ext_iff.1 h).2

@[to_additive Summable.prod]

Depends on / 依赖: Prod.ext_iff, comp_injective, ext_iff, h.comp_injective
-/
theorem Multipliable.prod_factor {f : β × γ -> α} (h : Multipliable f) (b : β) :
    Multipliable fun c => f (b, c) :=
  h.comp_injective fun _ _ h => (Prod.ext_iff.1 h).2

@[to_additive Summable.prod]
/--
lemma `Multipliable.prod` / 引理 `Multipliable.prod`

English:
lemma Multipliable.prod
  given: {f : β × γ -> α} (h : Multipliable f)
  proof: ((Equiv.sigmaEquivProd β γ).multipliable_iff.mpr h).sigma

@[to_additive]

中文:
引理 Multipliable.prod
  条件: {f : β × γ -> α} (h : Multipliable f)
  证明: ((Equiv.sigmaEquivProd β γ).multipliable_iff.mpr h).sigma

@[to_additive]

Depends on / 依赖: Equiv.sigmaEquivProd, multipliable_iff, multipliable_iff.mpr, sigmaEquivProd
-/
lemma Multipliable.prod {f : β × γ -> α} (h : Multipliable f) :
    Multipliable fun b => ∏' c, f (b, c) :=
  ((Equiv.sigmaEquivProd β γ).multipliable_iff.mpr h).sigma

@[to_additive]
/--
lemma `HasProd.tprod_fiberwise` / 引理 `HasProd.tprod_fiberwise`

English:
lemma HasProd.tprod_fiberwise
  given: [T2Space α] {f : β -> α} {a : α} (hf : HasProd f a) (g : β -> γ)
  proof: (((Equiv.sigmaFiberEquiv g).hasProd_iff).mpr hf).sigma
    fun _ => ((hf.multipliable.subtype _).hasProd_iff).mpr rfl

中文:
引理 HasProd.tprod_fiberwise
  条件: [T2Space α] {f : β -> α} {a : α} (hf : HasProd f a) (g : β -> γ)
  证明: (((Equiv.sigmaFiberEquiv g).hasProd_iff).mpr hf).sigma
    fun _ => ((hf.multipliable.subtype _).hasProd_iff).mpr rfl

Depends on / 依赖: Equiv.sigmaFiberEquiv, hasProd_iff, hf.multipliable.subtype, multipliable, sigmaFiberEquiv, subtype
-/
lemma HasProd.tprod_fiberwise [T2Space α] {f : β -> α} {a : α} (hf : HasProd f a) (g : β -> γ) :
    HasProd (fun c : γ => ∏' b : g ⁻¹' {c}, f b) a :=
(((Equiv.sigmaFiberEquiv g).hasProd_iff).mpr hf).sigma
    fun _ => ((hf.multipliable.subtype _).hasProd_iff).mpr rfl

section CompleteT0Space

variable [T0Space α]

@[to_additive]
/--
theorem `Multipliable.tprod_sigma` / 定理 `Multipliable.tprod_sigma`

English:
theorem Multipliable.tprod_sigma
  statement: {γ : β -> Type*} {f : (Σ b : β, γ b) -> α}
  proof: Multipliable.tprod_sigma' (fun b => ha.sigma_factor b) ha

@[to_additive Summable.tsum_prod]

中文:
定理 Multipliable.tprod_sigma
  结论: {γ : β -> 类型} {f : (Σ b : β, γ b) -> α}
  证明: Multipliable.tprod_sigma' (fun b => ha.sigma_factor b) ha

@[to_additive Summable.tsum_prod]
-/
protected theorem Multipliable.tprod_sigma {γ : β -> Type*} {f : (Σ b : β, γ b) -> α}
    (ha : Multipliable f) : ∏' p, f p = ∏' (b) (c), f ⟨b, c⟩ :=
  Multipliable.tprod_sigma' (fun b => ha.sigma_factor b) ha

@[to_additive Summable.tsum_prod]
/--
theorem `Multipliable.tprod_prod` / 定理 `Multipliable.tprod_prod`

English:
theorem Multipliable.tprod_prod
  given: {f : β × γ -> α} (h : Multipliable f)
  proof: h.tprod_prod' h.prod_factor

@[to_additive]

中文:
定理 Multipliable.tprod_prod
  条件: {f : β × γ -> α} (h : Multipliable f)
  证明: h.tprod_prod' h.prod_factor

@[to_additive]
-/
protected theorem Multipliable.tprod_prod {f : β × γ -> α} (h : Multipliable f) :
    ∏' p, f p = ∏' (b) (c), f ⟨b, c⟩ :=
  h.tprod_prod' h.prod_factor

@[to_additive]
/--
theorem `Multipliable.tprod_comm` / 定理 `Multipliable.tprod_comm`

English:
theorem Multipliable.tprod_comm
  given: {f : β -> γ -> α} (h : Multipliable (Function.uncurry f))
  proof: h.tprod_comm' h.prod_factor h.prod_symm.prod_factor

中文:
定理 Multipliable.tprod_comm
  条件: {f : β -> γ -> α} (h : Multipliable (Function.uncurry f))
  证明: h.tprod_comm' h.prod_factor h.prod_symm.prod_factor
-/
protected theorem Multipliable.tprod_comm {f : β -> γ -> α} (h : Multipliable (Function.uncurry f)) :
    ∏' (c) (b), f b c = ∏' (b) (c), f b c :=
  h.tprod_comm' h.prod_factor h.prod_symm.prod_factor

end CompleteT0Space

end CompleteSpace

section Pi

variable {ι : Type*} {X : α -> Type*} [forall x, CommMonoid (X x)] [forall x, TopologicalSpace (X x)]
  {L : SummationFilter ι}

@[to_additive]
/--
theorem `Pi.hasProd` / 定理 `Pi.hasProd`

English:
theorem Pi.hasProd
  given: {f : ι -> forall x, X x} {g : forall x, X x}
  proof: by
  simp only [HasProd, tendsto_pi_nhds, Finset.prod_apply]

@[to_additive]

中文:
定理 Pi.hasProd
  条件: {f : ι -> 对任意 x, X x} {g : 对任意 x, X x}
  证明: by
  simp only [HasProd, tendsto_pi_nhds, Finset.prod_apply]

@[to_additive]

Depends on / 依赖: Finset, Finset.prod_apply, HasProd, prod_apply, tendsto_pi_nhds
-/
theorem Pi.hasProd {f : ι -> forall x, X x} {g : forall x, X x} :
    HasProd f g L ↔ forall x, HasProd (fun i => f i x) (g x) L := by
  simp only [HasProd, tendsto_pi_nhds, Finset.prod_apply]

@[to_additive]
/--
theorem `Pi.multipliable` / 定理 `Pi.multipliable`

English:
theorem Pi.multipliable
  given: {f : ι -> forall x, X x}
  proof: by
  simp only [Multipliable, Pi.hasProd, Classical.skolem]

@[to_additive]

中文:
定理 Pi.multipliable
  条件: {f : ι -> 对任意 x, X x}
  证明: by
  simp only [Multipliable, Pi.hasProd, Classical.skolem]

@[to_additive]

Depends on / 依赖: Classical, Classical.skolem, Multipliable, Pi.hasProd, hasProd, skolem
-/
theorem Pi.multipliable {f : ι -> forall x, X x} :
    Multipliable f L ↔ forall x, Multipliable (fun i => f i x) L := by
  simp only [Multipliable, Pi.hasProd, Classical.skolem]

@[to_additive]
/--
theorem `tprod_apply` / 定理 `tprod_apply`

English:
theorem tprod_apply
  statement: [L.NeBot] [forall x, T2Space (X x)] {f : ι -> forall x, X x} {x : α}
  proof: (Pi.hasProd.mp hf.hasProd x).tprod_eq.symm

中文:
定理 tprod_apply
  结论: [L.NeBot] [对任意 x, T2Space (X x)] {f : ι -> 对任意 x, X x} {x : α}
  证明: (Pi.hasProd.mp hf.hasProd x).tprod_eq.symm

Depends on / 依赖: Pi.hasProd.mp, hasProd, hf.hasProd, tprod_eq, tprod_eq.symm
-/
theorem tprod_apply [L.NeBot] [forall x, T2Space (X x)] {f : ι -> forall x, X x} {x : α}
    (hf : Multipliable f L) : (∏'[L] i, f i) x = ∏'[L] i, f i x :=
  (Pi.hasProd.mp hf.hasProd x).tprod_eq.symm

end Pi


/-! ## Multiplicative opposite -/

section MulOpposite

open MulOpposite

variable [AddCommMonoid α] [TopologicalSpace α] {f : β -> α} {a : α}

/--
theorem `HasSum.op` / 定理 `HasSum.op`

English:
theorem HasSum.op
  given: (hf : HasSum f a L)
  statement: HasSum (fun a => op (f a)) (op a) L
  proof: (hf.map (@opAddEquiv α _) continuous_op :)

中文:
定理 HasSum.op
  条件: (hf : HasSum f a L)
  结论: HasSum (fun a => op (f a)) (op a) L
  证明: (hf.map (@opAddEquiv α _) continuous_op :)

Depends on / 依赖: continuous_op, hf.map, opAddEquiv
-/
theorem HasSum.op (hf : HasSum f a L) : HasSum (fun a => op (f a)) (op a) L :=
  (hf.map (@opAddEquiv α _) continuous_op :)

/--
theorem `Summable.op` / 定理 `Summable.op`

English:
theorem Summable.op
  given: (hf : Summable f L)
  statement: Summable (op ∘ f) L
  proof: hf.hasSum.op.summable

中文:
定理 Summable.op
  条件: (hf : Summable f L)
  结论: Summable (op ∘ f) L
  证明: hf.hasSum.op.summable

Depends on / 依赖: hasSum, hf.hasSum.op.summable, summable
-/
theorem Summable.op (hf : Summable f L) : Summable (op ∘ f) L :=
  hf.hasSum.op.summable

/--
theorem `HasSum.unop` / 定理 `HasSum.unop`

English:
theorem HasSum.unop
  given: {f : β -> αᵐᵒᵖ} {a : αᵐᵒᵖ} (hf : HasSum f a L)
  proof: (hf.map (@opAddEquiv α _).symm continuous_unop :)

中文:
定理 HasSum.unop
  条件: {f : β -> αᵐᵒᵖ} {a : αᵐᵒᵖ} (hf : HasSum f a L)
  证明: (hf.map (@opAddEquiv α _).symm continuous_unop :)

Depends on / 依赖: continuous_unop, hf.map, opAddEquiv
-/
theorem HasSum.unop {f : β -> αᵐᵒᵖ} {a : αᵐᵒᵖ} (hf : HasSum f a L) :
    HasSum (fun a => unop (f a)) (unop a) L :=
  (hf.map (@opAddEquiv α _).symm continuous_unop :)

/--
theorem `Summable.unop` / 定理 `Summable.unop`

English:
theorem Summable.unop
  given: {f : β -> αᵐᵒᵖ} (hf : Summable f L)
  statement: Summable (unop ∘ f) L
  proof: hf.hasSum.unop.summable

@[simp]

中文:
定理 Summable.unop
  条件: {f : β -> αᵐᵒᵖ} (hf : Summable f L)
  结论: Summable (unop ∘ f) L
  证明: hf.hasSum.unop.summable

@[simp]

Depends on / 依赖: hasSum, hf.hasSum.unop.summable, summable
-/
theorem Summable.unop {f : β -> αᵐᵒᵖ} (hf : Summable f L) : Summable (unop ∘ f) L :=
  hf.hasSum.unop.summable

@[simp]
/--
theorem `hasSum_op` / 定理 `hasSum_op`

English:
theorem hasSum_op
  statement: HasSum (fun a => op (f a)) (op a) L ↔ HasSum f a L
  proof: ⟨HasSum.unop, HasSum.op⟩

@[simp]

中文:
定理 hasSum_op
  结论: HasSum (fun a => op (f a)) (op a) L ↔ HasSum f a L
  证明: ⟨HasSum.unop, HasSum.op⟩

@[simp]

Depends on / 依赖: HasSum, HasSum.op, HasSum.unop
-/
theorem hasSum_op : HasSum (fun a => op (f a)) (op a) L ↔ HasSum f a L :=
  ⟨HasSum.unop, HasSum.op⟩

@[simp]
/--
theorem `hasSum_unop` / 定理 `hasSum_unop`

English:
theorem hasSum_unop
  given: {f : β -> αᵐᵒᵖ} {a : αᵐᵒᵖ}
  proof: ⟨HasSum.op, HasSum.unop⟩

@[simp]

中文:
定理 hasSum_unop
  条件: {f : β -> αᵐᵒᵖ} {a : αᵐᵒᵖ}
  证明: ⟨HasSum.op, HasSum.unop⟩

@[simp]

Depends on / 依赖: HasSum, HasSum.op, HasSum.unop
-/
theorem hasSum_unop {f : β -> αᵐᵒᵖ} {a : αᵐᵒᵖ} :
    HasSum (fun a => unop (f a)) (unop a) L ↔ HasSum f a L :=
  ⟨HasSum.op, HasSum.unop⟩

@[simp]
/--
theorem `summable_op` / 定理 `summable_op`

English:
theorem summable_op
  statement: (Summable (fun a => op (f a)) L) ↔ Summable f L
  proof: ⟨Summable.unop, Summable.op⟩

中文:
定理 summable_op
  结论: (Summable (fun a => op (f a)) L) ↔ Summable f L
  证明: ⟨Summable.unop, Summable.op⟩

Depends on / 依赖: Summable, Summable.op, Summable.unop
-/
theorem summable_op : (Summable (fun a => op (f a)) L) ↔ Summable f L :=
  ⟨Summable.unop, Summable.op⟩

/--
theorem `summable_unop` / 定理 `summable_unop`

English:
theorem summable_unop
  given: {f : β -> αᵐᵒᵖ}
  statement: (Summable (fun a => unop (f a)) L) ↔ Summable f L
  proof: ⟨Summable.op, Summable.unop⟩

中文:
定理 summable_unop
  条件: {f : β -> αᵐᵒᵖ}
  结论: (Summable (fun a => unop (f a)) L) ↔ Summable f L
  证明: ⟨Summable.op, Summable.unop⟩

Depends on / 依赖: Summable, Summable.op, Summable.unop
-/
theorem summable_unop {f : β -> αᵐᵒᵖ} : (Summable (fun a => unop (f a)) L) ↔ Summable f L :=
  ⟨Summable.op, Summable.unop⟩

/--
theorem `tsum_op` / 定理 `tsum_op`

English:
theorem tsum_op
  given: [T2Space α]
  statement: ∑'[L] x, op (f x) = op (∑'[L] x, f x)
  proof: (opHomeomorph.isClosedEmbedding.map_tsum f (g := opAddEquiv)).symm

中文:
定理 tsum_op
  条件: [T2Space α]
  结论: ∑'[L] x, op (f x) = op (∑'[L] x, f x)
  证明: (opHomeomorph.isClosedEmbedding.map_tsum f (g := opAddEquiv)).symm

Depends on / 依赖: isClosedEmbedding, map_tsum, opAddEquiv, opHomeomorph, opHomeomorph.isClosedEmbedding.map_tsum
-/
theorem tsum_op [T2Space α] : ∑'[L] x, op (f x) = op (∑'[L] x, f x) :=
  (opHomeomorph.isClosedEmbedding.map_tsum f (g := opAddEquiv)).symm

/--
theorem `tsum_unop` / 定理 `tsum_unop`

English:
theorem tsum_unop
  given: [T2Space α] {f : β -> αᵐᵒᵖ}
  statement: ∑'[L] x, unop (f x) = unop (∑'[L] x, f x)
  proof: op_injective tsum_op.symm

中文:
定理 tsum_unop
  条件: [T2Space α] {f : β -> αᵐᵒᵖ}
  结论: ∑'[L] x, unop (f x) = unop (∑'[L] x, f x)
  证明: op_injective tsum_op.symm

Depends on / 依赖: op_injective, tsum_op, tsum_op.symm
-/
theorem tsum_unop [T2Space α] {f : β -> αᵐᵒᵖ} : ∑'[L] x, unop (f x) = unop (∑'[L] x, f x) :=
  op_injective tsum_op.symm

end MulOpposite

/-! ## Interaction with the star -/

section ContinuousStar

variable [AddCommMonoid α] [TopologicalSpace α] [StarAddMonoid α] [ContinuousStar α] {f : β -> α}
  {a : α}

/--
theorem `HasSum.star` / 定理 `HasSum.star`

English:
theorem HasSum.star
  given: (h : HasSum f a L)
  statement: HasSum (fun b => star (f b)) (star a) L
  proof: by
  simpa only using! h.map (starAddEquiv : α ≃+ α) continuous_star

中文:
定理 HasSum.star
  条件: (h : HasSum f a L)
  结论: HasSum (fun b => star (f b)) (star a) L
  证明: by
  simpa only using! h.map (starAddEquiv : α ≃+ α) continuous_star

Depends on / 依赖: continuous_star, h.map, starAddEquiv
-/
theorem HasSum.star (h : HasSum f a L) : HasSum (fun b => star (f b)) (star a) L := by
  simpa only using! h.map (starAddEquiv : α ≃+ α) continuous_star

/--
theorem `Summable.star` / 定理 `Summable.star`

English:
theorem Summable.star
  given: (hf : Summable f L)
  statement: Summable (fun b => star (f b)) L
  proof: hf.hasSum.star.summable

中文:
定理 Summable.star
  条件: (hf : Summable f L)
  结论: Summable (fun b => star (f b)) L
  证明: hf.hasSum.star.summable

Depends on / 依赖: hasSum, hf.hasSum.star.summable, summable
-/
theorem Summable.star (hf : Summable f L) : Summable (fun b => star (f b)) L :=
  hf.hasSum.star.summable

/--
theorem `Summable.ofStar` / 定理 `Summable.ofStar`

English:
theorem Summable.ofStar
  given: (hf : Summable (fun b => Star.star (f b)) L)
  statement: Summable f L
  proof: by
  simpa only [star_star] using hf.star

@[simp]

中文:
定理 Summable.ofStar
  条件: (hf : Summable (fun b => Star.star (f b)) L)
  结论: Summable f L
  证明: by
  simpa only [star_star] using hf.star

@[simp]

Depends on / 依赖: hf.star, star_star
-/
theorem Summable.ofStar (hf : Summable (fun b => Star.star (f b)) L) : Summable f L := by
  simpa only [star_star] using hf.star

@[simp]
/--
theorem `summable_star_iff` / 定理 `summable_star_iff`

English:
theorem summable_star_iff
  statement: Summable (fun b => star (f b)) L ↔ Summable f L
  proof: ⟨Summable.ofStar, Summable.star⟩

@[simp]

中文:
定理 summable_star_iff
  结论: Summable (fun b => star (f b)) L ↔ Summable f L
  证明: ⟨Summable.ofStar, Summable.star⟩

@[simp]

Depends on / 依赖: Summable, Summable.ofStar, Summable.star, ofStar
-/
theorem summable_star_iff : Summable (fun b => star (f b)) L ↔ Summable f L :=
  ⟨Summable.ofStar, Summable.star⟩

@[simp]
/--
theorem `summable_star_iff'` / 定理 `summable_star_iff'`

English:
theorem summable_star_iff'
  statement: Summable (star f) L ↔ Summable f L
  proof: summable_star_iff

中文:
定理 summable_star_iff'
  结论: Summable (star f) L ↔ Summable f L
  证明: summable_star_iff

Depends on / 依赖: summable_star_iff
-/
theorem summable_star_iff' : Summable (star f) L ↔ Summable f L :=
  summable_star_iff

/--
theorem `tsum_star` / 定理 `tsum_star`

English:
theorem tsum_star
  given: [T2Space α]
  statement: star (∑'[L] b, f b) = ∑'[L] b, star (f b)
  proof: Function.LeftInverse.map_tsum (g := starAddEquiv) f continuous_star continuous_star star_star

中文:
定理 tsum_star
  条件: [T2Space α]
  结论: star (∑'[L] b, f b) = ∑'[L] b, star (f b)
  证明: Function.LeftInverse.map_tsum (g := starAddEquiv) f continuous_star continuous_star star_star

Depends on / 依赖: Function, Function.LeftInverse.map_tsum, LeftInverse, continuous_star, map_tsum, starAddEquiv, star_star
-/
theorem tsum_star [T2Space α] : star (∑'[L] b, f b) = ∑'[L] b, star (f b) :=
  Function.LeftInverse.map_tsum (g := starAddEquiv) f continuous_star continuous_star star_star

end ContinuousStar
