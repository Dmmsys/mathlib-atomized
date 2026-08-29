/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Topology.Connected.LocallyPathConnected
public import Mathlib.Topology.Covering.Quotient
public import Mathlib.Topology.Homotopy.Path
public import Mathlib.Topology.UnitInterval

/-!
# The homotopy lifting property for covering maps

- `IsCoveringMap.exists_path_lifts`, `IsCoveringMap.liftPath`: any path in the base of a covering
  map lifts uniquely to the covering space (given a lift of the starting point).

- `IsCoveringMap.liftHomotopy`: any homotopy `I × A → X` in the base of a covering map `E → X` can
  be lifted to a homotopy `I × A → E`, starting from a given lift of the restriction `{0} × A → X`.

- `IsCoveringMap.existsUnique_continuousMap_lifts`: any continuous map from a simply-connected,
  locally path-connected space lifts uniquely through a covering map (given a lift of an
  arbitrary point).
-/

noncomputable section

@[expose] public section

open Function Topology unitInterval

variable {E X A : Type*} [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace A] {p : E -> X}

namespace IsLocalHomeomorph

variable (homeo : IsLocalHomeomorph p)
include homeo

/--
theorem `exists_lift_nhds` / 定理 `exists_lift_nhds`

English:
theorem exists_lift_nhds
  statement: {f : C(I × A, X)} {g : I × A -> E} (g_lifts : p ∘ g = f)
  proof: by
  -- For every `e : E`, upgrade `p` to a LocalHomeomorph `q e` around `e`.
  choose q mem_source hpq using homeo
  /- Using the hypothesis `cont_a`, we partition the unit interval so that for each
    subinterval `[tₙ, tₙ₊₁]`, the image `g ([tₙ, tₙ₊₁] × {a})` is contained in the
    domain of som

中文:
定理 存在_lift_nhds
  结论: {f : C(I × A, X)} {g : I × A -> E} (g_lifts : p ∘ g = f)
  证明: by
  -- For every `e : E`, upgrade `p` to a LocalHomeomorph `q e` around `e`.
  choose q mem_source hpq using homeo
  /- Using the hypothesis `cont_a`, we partition the unit interval so that for each
    subinterval `[tₙ, tₙ₊₁]`, the image `g ([tₙ, tₙ₊₁] × {a})` is contained in the
    domain of som
-/
theorem exists_lift_nhds {f : C(I × A, X)} {g : I × A -> E} (g_lifts : p ∘ g = f)
    (cont_0 : Continuous (g ⟨0, ·⟩)) (a : A) (cont_a : Continuous (g ⟨·, a⟩)) :
    exists N in 𝓝 a, exists g' : I × A -> E, ContinuousOn g' (Set.univ ×ˢ N) ∧ p ∘ g' = f ∧
      (forall a, g' (0, a) = g (0, a)) ∧ forall t, g' (t, a) = g (t, a) := by
  -- For every `e : E`, upgrade `p` to a LocalHomeomorph `q e` around `e`.
  choose q mem_source hpq using homeo
  /- Using the hypothesis `cont_a`, we partition the unit interval so that for each
    subinterval `[tₙ, tₙ₊₁]`, the image `g ([tₙ, tₙ₊₁] × {a})` is contained in the
    domain of some local homeomorphism `q e`. -/
  obtain ⟨t, t_0, t_mono, ⟨n_max, h_max⟩, t_sub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (fun e => (q e).open_source.preimage cont_a)
      fun t _ => Set.mem_iUnion.mpr ⟨g (t, a), mem_source _⟩
  /- We aim to inductively prove the existence of Nₙ and g' continuous on [0, tₙ] × Nₙ for each n,
    and get the desired result by taking some n with tₙ = 1. -/
  suffices forall n, exists N, a in N ∧ IsOpen N ∧ exists g' : I × A -> E, ContinuousOn g' (Set.Icc 0 (t n) ×ˢ N) ∧
      p ∘ g' = f ∧ (forall a, g' (0, a) = g (0, a)) ∧ forall t' <= t n, g' (t', a) = g (t', a) by
    obtain ⟨N, haN, N_open, hN⟩ := this n_max
    simp_rw [h_max _ le_rfl] at hN
    refine ⟨N, N_open.mem_nhds haN, ?_⟩; convert! hN
    · rw [eq_comm, Set.eq_univ_iff_forall]; exact fun t => ⟨bot_le, le_top⟩
    · rw [imp_iff_right]; exact le_top
  refine Nat.rec ⟨_, Set.mem_univ a, isOpen_univ, g, ?_, g_lifts, fun a => rfl, fun _ _ => rfl⟩
    (fun n ⟨N, haN, N_open, g', cont_g', g'_lifts, g'_0, g'_a⟩ => ?_)
  · -- the n = 0 case is covered by the hypothesis cont_0.
    refine (cont_0.comp continuous_snd).continuousOn.congr (fun ta ⟨ht, _⟩ => ?_)
    rw [t_0]; rw [Set.Icc_self]; rw [Set.mem_singleton_iff] at ht; rw [← ta.eta, ht]; rfl
  /- Since g ([tₙ, tₙ₊₁] × {a}) is contained in the domain of some local homeomorphism `q e` and
    g lifts f, f ([tₙ, tₙ₊₁] × {a}) is contained in the codomain (`target`) of `q e`. -/
  obtain ⟨e, h_sub⟩ := t_sub n
  have : Set.Icc (t n) (t (n + 1)) ×ˢ {a} subseteq f ⁻¹' (q e).target := by
    rintro ⟨t0, a'⟩ ⟨ht, ha⟩
    rw [Set.mem_singleton_iff] at ha; dsimp only at ha
    rw [← g_lifts]; rw [hpq e]; rw [ha]
    exact (q e).map_source (h_sub ht)
  /- Using compactness of [tₙ, tₙ₊₁], we can find a neighborhood v of a such that
    f ([tₙ, tₙ₊₁] × v) is contained in the codomain of `q e`. -/
  obtain ⟨u, v, -, v_open, hu, hav, huv⟩ := generalized_tube_lemma isClosed_Icc.isCompact
    isCompact_singleton ((q e).open_target.preimage f.continuous) this
  classical
  /- Use the inverse of `q e` to extend g' from [0, tₙ] × Nₙ₊₁ to [0, tₙ₊₁] × Nₙ₊₁, where
    Nₙ₊₁ ⊆ v ∩ Nₙ is such that {tₙ} × Nₙ₊₁ is mapped to the domain (`source`) of `q e` by `g'`. -/
refine ⟨_, ?_, v_open.inter (cont_g'.comp (Continuous.prodMk_right <| t n).continuousOn
      fun a ha => ⟨?_, ha⟩).isOpen_inter_preimage N_open (q e).open_source,
    fun ta => if ta.1 <= t n then g' ta else if f ta in (q e).target then (q e).symm (f ta) else g ta,
    .if (fun ta ⟨⟨_, hav, _, ha⟩, hfr⟩ => ?_) (cont_g'.mono fun ta ⟨hta, ht⟩ => ?_) ?_,
    ?_, fun a => ?_, fun t0 htn1 => ?_⟩
  · refine ⟨Set.singleton_subset_iff.mp hav, haN, ?_⟩
    change g' (t n, a) in (q e).source; rw [g'_a _ le_rfl]
    exact h_sub ⟨le_rfl, t_mono n.le_succ⟩
  · rw [← t_0]; exact ⟨t_mono n.zero_le, le_rfl⟩
  · have ht := Set.mem_ofPred.mp (frontier_le_subset_eq continuous_fst continuous_const hfr)
    have : f ta in (q e).target := huv ⟨hu (by rw [ht]; exact ⟨le_rfl, t_mono n.le_succ⟩), hav⟩
    rw [if_pos this]
    -- here we use that {tₙ} × Nₙ₊₁ is mapped to the domain of `q e`
    apply (q e).injOn (by rwa [← ta.eta, ht]) ((q e).map_target this)
    rw [(q e).right_inv this]; rw [← hpq e]; exact congr($g'_lifts ta)
  · rw [closure_le_eq continuous_fst continuous_const] at ht
    exact ⟨⟨hta.1.1, ht⟩, hta.2.2.1⟩
  · simp_rw [not_le]; exact (ContinuousOn.congr ((q e).continuousOn_invFun.comp f.2.continuousOn
      fun _ h => huv ⟨hu ⟨h.2, h.1.1.2⟩, h.1.2.1⟩)
fun _ h => if_pos huv ⟨hu ⟨h.2, h.1.1.2⟩, h.1.2.1⟩).mono
        (Set.inter_subset_inter_right _ <| closure_lt_subset_le continuous_const continuous_fst)
  · ext ta; rw [Function.comp_apply]; split_ifs with _ hv
    · exact congr($g'_lifts ta)
    · rw [hpq e, (q e).right_inv hv]
    · exact congr($g_lifts ta)
  · rw [← g'_0]; exact if_pos bot_le
  · dsimp only; split_ifs with htn hf
    · exact g'_a t0 htn
    · apply (q e).injOn ((q e).map_target hf) (h_sub ⟨le_of_not_ge htn, htn1⟩)
      rw [(q e).right_inv hf]; rw [← hpq e]; exact congr($g_lifts _).symm
    · rfl

variable (sep : IsSeparatedMap p)
include sep

/--
theorem `continuous_lift` / 定理 `continuous_lift`

English:
theorem continuous_lift
  statement: (f : C(I × A, X)) {g : I × A -> E} (g_lifts : p ∘ g = f)
  proof: by
  rw [continuous_iff_continuousAt]
  intro ⟨t, a⟩
  obtain ⟨N, haN, g', cont_g', g'_lifts, g'_0, -⟩ :=
    homeo.exists_lift_nhds g_lifts cont_0 a (cont_A a)
  refine (cont_g'.congr fun ⟨t, a⟩ ⟨_, ha⟩ => ?_).continuousAt (prod_mem_nhds Filter.univ_mem haN)
  refine congr_fun (sep.eq_of_comp_eq ho

中文:
定理 continuous_lift
  结论: (f : C(I × A, X)) {g : I × A -> E} (g_lifts : p ∘ g = f)
  证明: by
  rw [continuous_iff_continuousAt]
  intro ⟨t, a⟩
  obtain ⟨N, haN, g', cont_g', g'_lifts, g'_0, -⟩ :=
    homeo.exists_lift_nhds g_lifts cont_0 a (cont_A a)
  refine (cont_g'.congr fun ⟨t, a⟩ ⟨_, ha⟩ => ?_).continuousAt (prod_mem_nhds Filter.univ_mem haN)
  refine congr_fun (sep.eq_of_comp_eq ho

Depends on / 依赖: Filter, Filter.univ_mem, _lifts, _lifts.symm, comp_continuous, congr_fun, cont_0, cont_A, cont_g, continuousAt, continuous_iff_continuousAt, eq_of_comp_eq, exists_lift_nhds, g_lifts, g_lifts.trans, homeo.exists_lift_nhds, homeo.isLocallyInjective, isLocallyInjective, prodMk_left, prod_mem_nhds
-/
theorem continuous_lift (f : C(I × A, X)) {g : I × A -> E} (g_lifts : p ∘ g = f)
    (cont_0 : Continuous (g ⟨0, ·⟩)) (cont_A : forall a, Continuous (g ⟨·, a⟩)) : Continuous g := by
  rw [continuous_iff_continuousAt]
  intro ⟨t, a⟩
  obtain ⟨N, haN, g', cont_g', g'_lifts, g'_0, -⟩ :=
    homeo.exists_lift_nhds g_lifts cont_0 a (cont_A a)
  refine (cont_g'.congr fun ⟨t, a⟩ ⟨_, ha⟩ => ?_).continuousAt (prod_mem_nhds Filter.univ_mem haN)
  refine congr_fun (sep.eq_of_comp_eq homeo.isLocallyInjective (cont_A a)
    (cont_g'.comp_continuous (.prodMk_left a) fun _ => ⟨⟨⟩, ha⟩) ?_ 0 (g'_0 a).symm) t
  ext t; apply congr_fun (g_lifts.trans g'_lifts.symm)

/--
theorem `monodromy_theorem` / 定理 `monodromy_theorem`

English:
theorem monodromy_theorem
  statement: {γ₀ γ₁ : C(I, X)} (γ : γ₀.HomotopyRel γ₁ {0,1}) (Γ : I -> C(I, E))
  proof: by
  have := homeo.continuous_lift sep (.comp γ .prodSwap) (g := fun st => Γ st.2 st.1) ?_ ?_ ?_
  · apply sep.const_of_comp homeo.isLocallyInjective (this.comp (.prodMk_right 1))
    intro t t'; change p (Γ _ _) = p (Γ _ _); simp_rw [Γ_lifts, γ.eq_fst _ (.inr rfl)]
  · ext; apply Γ_lifts
  · simp_r

中文:
定理 monodromy_theorem
  结论: {γ₀ γ₁ : C(I, X)} (γ : γ₀.HomotopyRel γ₁ {0,1}) (Γ : I -> C(I, E))
  证明: by
  have := homeo.continuous_lift sep (.comp γ .prodSwap) (g := fun st => Γ st.2 st.1) ?_ ?_ ?_
  · apply sep.const_of_comp homeo.isLocallyInjective (this.comp (.prodMk_right 1))
    intro t t'; change p (Γ _ _) = p (Γ _ _); simp_rw [Γ_lifts, γ.eq_fst _ (.inr rfl)]
  · ext; apply Γ_lifts
  · simp_r

Depends on / 依赖: const_of_comp, continuous_const, continuous_lift, eq_fst, homeo.continuous_lift, homeo.isLocallyInjective, isLocallyInjective, prodMk_right, prodSwap, sep.const_of_comp, simp_rw, this.comp
-/
theorem monodromy_theorem {γ₀ γ₁ : C(I, X)} (γ : γ₀.HomotopyRel γ₁ {0,1}) (Γ : I -> C(I, E))
    (Γ_lifts : forall t s, p (Γ t s) = γ (t, s)) (Γ_0 : forall t, Γ t 0 = Γ 0 0) (t : I) :
    Γ t 1 = Γ 0 1 := by
  have := homeo.continuous_lift sep (.comp γ .prodSwap) (g := fun st => Γ st.2 st.1) ?_ ?_ ?_
  · apply sep.const_of_comp homeo.isLocallyInjective (this.comp (.prodMk_right 1))
    intro t t'; change p (Γ _ _) = p (Γ _ _); simp_rw [Γ_lifts, γ.eq_fst _ (.inr rfl)]
  · ext; apply Γ_lifts
  · simp_rw [Γ_0]; exact continuous_const
  · exact fun t => (Γ t).2

omit sep
open PathConnectedSpace (somePath) in
/--
theorem `existsUnique_continuousMap_lifts` / 定理 `existsUnique_continuousMap_lifts`

English:
theorem existsUnique_continuousMap_lifts
  statement: [PathConnectedSpace A] [LocallyPathConnectedSpace A]
  proof: by
  choose Γ Γ_0 Γ_lifts using ex
  let F (a : A) : E := Γ _ (somePath a₀ a).source 1
  have (a : A) : p (F a) = f a := by simpa using congr_fun (Γ_lifts _ (Path.source _)) 1
  refine ⟨⟨F, continuous_iff_continuousAt.mpr fun a => ?_⟩, ⟨?_, funext this⟩, fun F' ⟨F'_0, hpF'⟩ =>
    DFunLike.ext _ _ f

中文:
定理 存在Unique_continuousMap_lifts
  结论: [道路连通空间 A] [LocallyPathConnected空间 A]
  证明: by
  choose Γ Γ_0 Γ_lifts using ex
  let F (a : A) : E := Γ _ (somePath a₀ a).source 1
  have (a : A) : p (F a) = f a := by simpa using congr_fun (Γ_lifts _ (Path.source _)) 1
  refine ⟨⟨F, continuous_iff_continuousAt.mpr fun a => ?_⟩, ⟨?_, funext this⟩, fun F' ⟨F'_0, hpF'⟩ =>
    DFunLike.ext _ _ f

Depends on / 依赖: ContinuousAt, ContinuousAt.congr, DFunLike, DFunLike.ext, Path.source, congr_fun, continuousA, continuousAt_symm, continuous_iff_continuousAt, continuous_iff_continuousAt.mpr, map_source, p.continuousAt_symm, p.map_source, p.symm, p.target, somePath, source, target
-/
theorem existsUnique_continuousMap_lifts [PathConnectedSpace A] [LocallyPathConnectedSpace A]
    (f : C(A, X)) (a₀ : A) (e₀ : E) (he : p e₀ = f a₀)
    (ex : forall γ : C(I, A), γ 0 = a₀ -> exists Γ : C(I, E), Γ 0 = e₀ ∧ p ∘ Γ = f.comp γ)
    (uniq : forall γ γ' : C(I, A), forall Γ Γ' : C(I, E), γ 0 = a₀ -> γ' 0 = a₀ -> Γ 0 = e₀ -> Γ' 0 = e₀ ->
      p ∘ Γ = f.comp γ -> p ∘ Γ' = f.comp γ' -> γ 1 = γ' 1 -> Γ 1 = Γ' 1) :
    exists! F : C(A, E), F a₀ = e₀ ∧ p ∘ F = f := by
  choose Γ Γ_0 Γ_lifts using ex
  let F (a : A) : E := Γ _ (somePath a₀ a).source 1
  have (a : A) : p (F a) = f a := by simpa using congr_fun (Γ_lifts _ (Path.source _)) 1
  refine ⟨⟨F, continuous_iff_continuousAt.mpr fun a => ?_⟩, ⟨?_, funext this⟩, fun F' ⟨F'_0, hpF'⟩ =>
    DFunLike.ext _ _ fun a => ?_⟩
  · obtain ⟨p, hep, rfl⟩ := homeo (F a)
    have hfap : f a in p.target := by rw [← this]; exact p.map_source hep
    refine ContinuousAt.congr (f := p.symm ∘ f)
      ((p.continuousAt_symm hfap).comp f.2.continuousAt) ?_
    have ⟨U, ⟨haU, U_conn⟩, hUp⟩ := (path_connected_basis a).mem_iff.mp
      ((p.open_target.preimage f.continuous).mem_nhds hfap)
    refine Filter.mem_of_superset haU fun x hxU => ?_
    have ⟨γ, hγ⟩ := U_conn.joinedIn _ (mem_of_mem_nhds haU) _ hxU
    let Γ' : Path e₀ ((p.symm ∘ f) a) :=
      ⟨Γ _ (somePath a₀ a).source, Γ_0 .., by simp [← this, hep, F]⟩
    specialize uniq ((somePath a₀ a).trans γ) _ (Γ'.trans <| γ.map' <| p.continuousOn_symm.comp
f.2.continuousOn by rintro _ ⟨t, rfl⟩; exact hUp (hγ _)) _ (by simp) (somePath a₀ x).source
      (by simp) (Γ_0 _ (somePath a₀ x).source) _ (Γ_lifts ..) (by simp)
    · ext
      simp only [Function.comp, ContinuousMap.coe_coe, Path.trans_apply, ContinuousMap.coe_comp]
      split_ifs
      · apply congr_fun (Γ_lifts ..)
      · simp [Path.map', p.right_inv (hUp (hγ _))]
    simpa using uniq
  · exact uniq _ (.const I a₀) _ (.const I e₀) (somePath a₀ a₀).source rfl (Γ_0 ..) rfl (Γ_lifts ..)
      (by simpa) (Path.target _)
  · let γ := somePath a₀ a
    simpa using uniq _ _ (F'.comp γ) (Γ _ γ.source) γ.source γ.source (by simpa) (Γ_0 ..)
      (by simp [← Function.comp_assoc, hpF']) (Γ_lifts ..) rfl

end IsLocalHomeomorph

namespace IsCoveringMap
variable (cov : IsCoveringMap p)
include cov

section path_lifting
variable (γ : C(I, X)) (e : E) (γ_0 : γ 0 = p e)
include γ_0

/--
theorem `exists_path_lifts` / 定理 `exists_path_lifts`

English:
theorem exists_path_lifts
  statement: exists Γ : C(I, E), p ∘ Γ = γ ∧ Γ 0 = e
  proof: by
  let U x := (cov x).2.choose
  choose mem_base U_open _ H _ using fun x => (cov x).2.choose_spec
  obtain ⟨t, t_0, t_mono, ⟨n_max, h_max⟩, t_sub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
    (fun x => (U_open x).preimage γ.continuous) fun t _ => Set.mem_iUnion.2 ⟨γ t, mem_base _

中文:
定理 存在_path_lifts
  结论: 存在 Γ : C(I, E), p ∘ Γ = γ ∧ Γ 0 = e
  证明: by
  let U x := (cov x).2.choose
  choose mem_base U_open _ H _ using fun x => (cov x).2.choose_spec
  obtain ⟨t, t_0, t_mono, ⟨n_max, h_max⟩, t_sub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
    (fun x => (U_open x).preimage γ.continuous) fun t _ => Set.mem_iUnion.2 ⟨γ t, mem_base _

Depends on / 依赖: ContinuousOn, Set.Icc, Set.mem_iUnion, U_open, choose_spec, continu, continuous, exists_monotone_Icc_subset_open_cover_unitInterval, h_max, le_rfl, mem_base, mem_iUnion, n_max, preimage, t_mono, t_sub
-/
theorem exists_path_lifts : exists Γ : C(I, E), p ∘ Γ = γ ∧ Γ 0 = e := by
  let U x := (cov x).2.choose
  choose mem_base U_open _ H _ using fun x => (cov x).2.choose_spec
  obtain ⟨t, t_0, t_mono, ⟨n_max, h_max⟩, t_sub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
    (fun x => (U_open x).preimage γ.continuous) fun t _ => Set.mem_iUnion.2 ⟨γ t, mem_base _⟩
  suffices forall n, exists Γ : I -> E, ContinuousOn Γ (Set.Icc 0 (t n)) ∧
      (Set.Icc 0 (t n)).EqOn (p ∘ Γ) γ ∧ Γ 0 = e by
    obtain ⟨Γ, cont, eqOn, Γ_0⟩ := this n_max
    rw [h_max _ le_rfl] at cont eqOn
    exact ⟨⟨Γ, continuousOn_univ.mp
      (by convert! cont; rw [eq_comm, Set.eq_univ_iff_forall]; exact fun t => ⟨bot_le, le_top⟩)⟩,
      funext fun _ => eqOn ⟨bot_le, le_top⟩, Γ_0⟩
  intro n
  induction n with
  | zero =>
    refine ⟨fun _ => e, continuous_const.continuousOn, fun t ht => ?_, rfl⟩
    rw [t_0]; rw [Set.Icc_self]; rw [Set.mem_singleton_iff] at ht; subst ht; exact γ_0.symm
  | succ n ih => ?_
  obtain ⟨Γ, cont, eqOn, Γ_0⟩ := ih
  obtain ⟨x, t_sub⟩ := t_sub n
  have pΓtn : p (Γ (t n)) = γ (t n) := eqOn ⟨t_0 ▸ t_mono n.zero_le, le_rfl⟩
  have : Nonempty (p ⁻¹' {x}) :=
    ⟨(H x ⟨Γ (t n), Set.mem_preimage.mpr (pΓtn ▸ t_sub ⟨le_rfl, t_mono n.le_succ⟩)⟩).2⟩
  let q := (cov x).toTrivialization
  refine ⟨fun s => if s <= t n then Γ s else q.invFun (γ s, (q (Γ (t n))).2),
    .if (fun s hs => ?_) (cont.mono fun _ h => ?_) ?_, fun s hs => ?_, ?_⟩
  · cases frontier_Iic_subset _ hs.2
    rw [← pΓtn]
    refine (q.symm_apply_mk_proj ?_).symm
    rw [q.mem_source]; rw [pΓtn]
    exact t_sub ⟨le_rfl, t_mono n.le_succ⟩
  · rw [closure_le_eq continuous_id' continuous_const] at h; exact ⟨h.1.1, h.2⟩
  · apply q.continuousOn_invFun.comp ((Continuous.prodMk_left _).comp γ.2).continuousOn
    simp_rw [not_le, q.target_eq]; intro s h
    exact ⟨t_sub ⟨closure_lt_subset_le continuous_const continuous_subtype_val h.2, h.1.2⟩, ⟨⟩⟩
  · rw [Function.comp_apply]; split_ifs with h
    exacts [eqOn ⟨hs.1, h⟩, q.proj_symm_apply' (t_sub ⟨le_of_not_ge h, hs.2⟩)]
  · dsimp only; rwa [if_pos (t_0 ▸ t_mono n.zero_le)]

/--
Definition of `liftPath` / `liftPath` 的定义

English:
definition liftPath
  signature: : C(I, E)
  body: (cov.exists_path_lifts γ e γ_0).choose

中文:
定义 liftPath
  签名: : C(I, E)
  定义体: (cov.exists_path_lifts γ e γ_0).choose

Depends on / 依赖: cov.exists_path_lifts, exists_path_lifts
-/
def liftPath : C(I, E) := (cov.exists_path_lifts γ e γ_0).choose

/--
lemma `liftPath_lifts` / 引理 `liftPath_lifts`

English:
lemma liftPath_lifts
  statement: p ∘ cov.liftPath γ e γ_0 = γ
  proof: (cov.exists_path_lifts γ e γ_0).choose_spec.1

中文:
引理 liftPath_lifts
  结论: p ∘ cov.liftPath γ e γ_0 = γ
  证明: (cov.exists_path_lifts γ e γ_0).choose_spec.1

Depends on / 依赖: choose_spec, cov.exists_path_lifts, exists_path_lifts
-/
lemma liftPath_lifts : p ∘ cov.liftPath γ e γ_0 = γ := (cov.exists_path_lifts γ e γ_0).choose_spec.1
/--
lemma `liftPath_zero` / 引理 `liftPath_zero`

English:
lemma liftPath_zero
  statement: cov.liftPath γ e γ_0 0 = e
  proof: (cov.exists_path_lifts γ e γ_0).choose_spec.2

中文:
引理 liftPath_zero
  结论: cov.liftPath γ e γ_0 0 = e
  证明: (cov.exists_path_lifts γ e γ_0).choose_spec.2

Depends on / 依赖: choose_spec, cov.exists_path_lifts, exists_path_lifts
-/
lemma liftPath_zero : cov.liftPath γ e γ_0 0 = e := (cov.exists_path_lifts γ e γ_0).choose_spec.2

variable {γ e}
/--
lemma `eq_liftPath_iff` / 引理 `eq_liftPath_iff`

English:
lemma eq_liftPath_iff
  given: {Γ : I -> E}
  statement: Γ = cov.liftPath γ e γ_0 ↔ Continuous Γ ∧ p ∘ Γ = γ ∧ Γ 0 = e
  proof: have lifts := cov.liftPath_lifts γ e γ_0
  have zero := cov.liftPath_zero γ e γ_0
  ⟨(· ▸ ⟨(cov.liftPath γ e γ_0).2, lifts, zero⟩), fun ⟨Γ_cont, Γ_lifts, Γ_0⟩ => cov.eq_of_comp_eq
    Γ_cont (cov.liftPath γ e γ_0).continuous (Γ_lifts ▸ lifts.symm) 0 (Γ_0 ▸ zero.symm)⟩

中文:
引理 eq_liftPath_iff
  条件: {Γ : I -> E}
  结论: Γ = cov.liftPath γ e γ_0 ↔ 连续 Γ ∧ p ∘ Γ = γ ∧ Γ 0 = e
  证明: have lifts := cov.liftPath_lifts γ e γ_0
  have zero := cov.liftPath_zero γ e γ_0
  ⟨(· ▸ ⟨(cov.liftPath γ e γ_0).2, lifts, zero⟩), fun ⟨Γ_cont, Γ_lifts, Γ_0⟩ => cov.eq_of_comp_eq
    Γ_cont (cov.liftPath γ e γ_0).continuous (Γ_lifts ▸ lifts.symm) 0 (Γ_0 ▸ zero.symm)⟩

Depends on / 依赖: continuous, cov.eq_of_comp_eq, cov.liftPath, cov.liftPath_lifts, cov.liftPath_zero, eq_of_comp_eq, liftPath, liftPath_lifts, liftPath_zero, lifts.symm, zero.symm
-/
lemma eq_liftPath_iff {Γ : I -> E} : Γ = cov.liftPath γ e γ_0 ↔ Continuous Γ ∧ p ∘ Γ = γ ∧ Γ 0 = e :=
  have lifts := cov.liftPath_lifts γ e γ_0
  have zero := cov.liftPath_zero γ e γ_0
  ⟨(· ▸ ⟨(cov.liftPath γ e γ_0).2, lifts, zero⟩), fun ⟨Γ_cont, Γ_lifts, Γ_0⟩ => cov.eq_of_comp_eq
    Γ_cont (cov.liftPath γ e γ_0).continuous (Γ_lifts ▸ lifts.symm) 0 (Γ_0 ▸ zero.symm)⟩

/--
lemma `eq_liftPath_iff'` / 引理 `eq_liftPath_iff'`

English:
lemma eq_liftPath_iff'
  given: {Γ : C(I, E)}
  statement: Γ = cov.liftPath γ e γ_0 ↔ p ∘ Γ = γ ∧ Γ 0 = e
  proof: by
  simp_rw [← DFunLike.coe_fn_eq, eq_liftPath_iff, and_iff_right (ContinuousMap.continuous _)]

omit γ_0

中文:
引理 eq_liftPath_iff'
  条件: {Γ : C(I, E)}
  结论: Γ = cov.liftPath γ e γ_0 ↔ p ∘ Γ = γ ∧ Γ 0 = e
  证明: by
  simp_rw [← DFunLike.coe_fn_eq, eq_liftPath_iff, and_iff_right (ContinuousMap.continuous _)]

omit γ_0

Depends on / 依赖: ContinuousMap, ContinuousMap.continuous, DFunLike, DFunLike.coe_fn_eq, and_iff_right, coe_fn_eq, continuous, eq_liftPath_iff, simp_rw
-/
lemma eq_liftPath_iff' {Γ : C(I, E)} : Γ = cov.liftPath γ e γ_0 ↔ p ∘ Γ = γ ∧ Γ 0 = e := by
  simp_rw [← DFunLike.coe_fn_eq, eq_liftPath_iff, and_iff_right (ContinuousMap.continuous _)]

omit γ_0
/--
lemma `liftPath_const` / 引理 `liftPath_const`

English:
lemma liftPath_const
  given: {x : X} (hpe : x = p e)
  statement: cov.liftPath (.const I x) e hpe = .const I e
  proof: .symm (cov.eq_liftPath_iff' _).mpr ⟨funext fun _ => hpe.symm, rfl⟩

中文:
引理 liftPath_const
  条件: {x : X} (hpe : x = p e)
  结论: cov.liftPath (.const I x) e hpe = .const I e
  证明: .symm (cov.eq_liftPath_iff' _).mpr ⟨funext fun _ => hpe.symm, rfl⟩

Depends on / 依赖: cov.eq_liftPath_iff, eq_liftPath_iff, hpe.symm
-/
lemma liftPath_const {x : X} (hpe : x = p e) : cov.liftPath (.const I x) e hpe = .const I e :=
.symm (cov.eq_liftPath_iff' _).mpr ⟨funext fun _ => hpe.symm, rfl⟩

/--
lemma `liftPath_trans` / 引理 `liftPath_trans`

English:
lemma liftPath_trans
  given: {x y z : X} {e : E} (hpe : x = p e) (γ : Path x y) (γ' : Path y z)
  proof: cov.liftPath γ e (γ.source.trans hpe)
    cov.liftPath (γ.trans γ') e (by simpa) = (⟨Γ, liftPath_zero .., rfl⟩ : Path e (Γ 1)).trans
      ⟨cov.liftPath γ' (Γ 1) (by simpa using congr($(cov.liftPath_lifts γ ..) 1).symm),
        liftPath_zero .., rfl⟩ := by
refine .symm (cov.eq_liftPath_iff' _).mpr 

中文:
引理 liftPath_trans
  条件: {x y z : X} {e : E} (hpe : x = p e) (γ : 道路 x y) (γ' : 道路 y z)
  证明: cov.liftPath γ e (γ.source.trans hpe)
    cov.liftPath (γ.trans γ') e (by simpa) = (⟨Γ, liftPath_zero .., rfl⟩ : Path e (Γ 1)).trans
      ⟨cov.liftPath γ' (Γ 1) (by simpa using congr($(cov.liftPath_lifts γ ..) 1).symm),
        liftPath_zero .., rfl⟩ := by
refine .symm (cov.eq_liftPath_iff' _).mpr 

Depends on / 依赖: cov.liftPath, liftPath, source, source.trans
-/
lemma liftPath_trans {x y z : X} {e : E} (hpe : x = p e) (γ : Path x y) (γ' : Path y z) :
    letI Γ := cov.liftPath γ e (γ.source.trans hpe)
    cov.liftPath (γ.trans γ') e (by simpa) = (⟨Γ, liftPath_zero .., rfl⟩ : Path e (Γ 1)).trans
      ⟨cov.liftPath γ' (Γ 1) (by simpa using congr($(cov.liftPath_lifts γ ..) 1).symm),
        liftPath_zero .., rfl⟩ := by
refine .symm (cov.eq_liftPath_iff' _).mpr ⟨funext fun _ => ?_, by simp⟩
  simp only [ContinuousMap.coe_coe, Function.comp_apply, Path.trans_apply]; split_ifs
  · exact congr_fun (cov.liftPath_lifts γ e (γ.source.trans hpe)) _
  · refine congr_fun (cov.liftPath_lifts γ' _ ?_) _
    simpa using congr($(cov.liftPath_lifts γ ..) 1).symm

end path_lifting

section homotopy_lifting
variable (H : C(I × A, X)) (f : C(A, E)) (H_0 : forall a, H (0, a) = p (f a))

/--
Definition of `liftHomotopy` / `liftHomotopy` 的定义

English:
definition liftHomotopy
  signature: : C(I × A, E) where
  body: cov.liftPath (H.comp <| (ContinuousMap.id I).prodMk <| .const I ta.2)
    (f ta.2) (H_0 ta.2) ta.1
  continuous_toFun := cov.isLocalHomeomorph.continuous_lift cov.isSeparatedMap H
    (by ext ⟨t, a⟩; exact congr_fun (cov.liftPath_lifts ..) t)
    (by convert! f.continuous with a; exact cov.liftPath_

中文:
定义 liftHomotopy
  签名: : C(I × A, E) where
  定义体: cov.liftPath (H.comp <| (ContinuousMap.id I).prodMk <| .const I ta.2)
    (f ta.2) (H_0 ta.2) ta.1
  continuous_toFun := cov.isLocalHomeomorph.continuous_lift cov.isSeparatedMap H
    (by ext ⟨t, a⟩; exact congr_fun (cov.liftPath_lifts ..) t)
    (by convert! f.continuous with a; exact cov.liftPath_
-/
@[simps] def liftHomotopy : C(I × A, E) where
  toFun ta := cov.liftPath (H.comp <| (ContinuousMap.id I).prodMk <| .const I ta.2)
    (f ta.2) (H_0 ta.2) ta.1
  continuous_toFun := cov.isLocalHomeomorph.continuous_lift cov.isSeparatedMap H
    (by ext ⟨t, a⟩; exact congr_fun (cov.liftPath_lifts ..) t)
    (by convert! f.continuous with a; exact cov.liftPath_zero ..)
    fun a => by dsimp only; exact (cov.liftPath (γ_0 := by simp [*])).2

/--
lemma `liftHomotopy_lifts` / 引理 `liftHomotopy_lifts`

English:
lemma liftHomotopy_lifts
  statement: p ∘ cov.liftHomotopy H f H_0 = H
  proof: funext fun ⟨t, _⟩ => congr_fun (cov.liftPath_lifts ..) t

中文:
引理 liftHomotopy_lifts
  结论: p ∘ cov.liftHomotopy H f H_0 = H
  证明: funext fun ⟨t, _⟩ => congr_fun (cov.liftPath_lifts ..) t

Depends on / 依赖: congr_fun, cov.liftPath_lifts, liftPath_lifts
-/
lemma liftHomotopy_lifts : p ∘ cov.liftHomotopy H f H_0 = H :=
  funext fun ⟨t, _⟩ => congr_fun (cov.liftPath_lifts ..) t

/--
lemma `liftHomotopy_zero` / 引理 `liftHomotopy_zero`

English:
lemma liftHomotopy_zero
  given: (a : A)
  statement: cov.liftHomotopy H f H_0 (0, a) = f a
  proof: cov.liftPath_zero ..

中文:
引理 liftHomotopy_zero
  条件: (a : A)
  结论: cov.liftHomotopy H f H_0 (0, a) = f a
  证明: cov.liftPath_zero ..

Depends on / 依赖: cov.liftPath_zero, liftPath_zero
-/
lemma liftHomotopy_zero (a : A) : cov.liftHomotopy H f H_0 (0, a) = f a := cov.liftPath_zero ..

variable {H f}
/--
lemma `eq_liftHomotopy_iff` / 引理 `eq_liftHomotopy_iff`

English:
lemma eq_liftHomotopy_iff
  given: (H' : I × A -> E)
  statement: H' = cov.liftHomotopy H f H_0 ↔
  proof: by
  refine ⟨?_, fun ⟨H'_cont, H'_lifts, H'_0⟩ => funext fun ⟨t, a⟩ => ?_⟩
  · rintro rfl; refine ⟨fun a => ?_, cov.liftHomotopy_lifts H f H_0, cov.liftHomotopy_zero H f H_0⟩
    simp_rw [liftHomotopy_apply]; exact (cov.liftPath _ _ <| H_0 a).2
  · apply congr_fun ((cov.eq_liftPath_iff _).mpr ⟨H'_co

中文:
引理 eq_liftHomotopy_iff
  条件: (H' : I × A -> E)
  结论: H' = cov.liftHomotopy H f H_0 ↔
  证明: by
  refine ⟨?_, fun ⟨H'_cont, H'_lifts, H'_0⟩ => funext fun ⟨t, a⟩ => ?_⟩
  · rintro rfl; refine ⟨fun a => ?_, cov.liftHomotopy_lifts H f H_0, cov.liftHomotopy_zero H f H_0⟩
    simp_rw [liftHomotopy_apply]; exact (cov.liftPath _ _ <| H_0 a).2
  · apply congr_fun ((cov.eq_liftPath_iff _).mpr ⟨H'_co

Depends on / 依赖: _cont, _lifts, congr_fun, cov.eq_liftPath_iff, cov.liftHomotopy_lifts, cov.liftHomotopy_zero, cov.liftPath, eq_liftPath_iff, liftHomotopy_apply, liftHomotopy_lifts, liftHomotopy_zero, liftPath, simp_rw
-/
lemma eq_liftHomotopy_iff (H' : I × A -> E) : H' = cov.liftHomotopy H f H_0 ↔
    (forall a, Continuous (H' ⟨·, a⟩)) ∧ p ∘ H' = H ∧ forall a, H' (0, a) = f a := by
  refine ⟨?_, fun ⟨H'_cont, H'_lifts, H'_0⟩ => funext fun ⟨t, a⟩ => ?_⟩
  · rintro rfl; refine ⟨fun a => ?_, cov.liftHomotopy_lifts H f H_0, cov.liftHomotopy_zero H f H_0⟩
    simp_rw [liftHomotopy_apply]; exact (cov.liftPath _ _ <| H_0 a).2
  · apply congr_fun ((cov.eq_liftPath_iff _).mpr ⟨H'_cont a, _, H'_0 a⟩) t
    ext ⟨t, a⟩; exact congr_fun H'_lifts _

/--
lemma `eq_liftHomotopy_iff'` / 引理 `eq_liftHomotopy_iff'`

English:
lemma eq_liftHomotopy_iff'
  given: (H' : C(I × A, E))
  proof: by
  simp_rw [← DFunLike.coe_fn_eq, eq_liftHomotopy_iff]
  exact and_iff_right fun a => H'.2.comp (.prodMk_left a)

中文:
引理 eq_liftHomotopy_iff'
  条件: (H' : C(I × A, E))
  证明: by
  simp_rw [← DFunLike.coe_fn_eq, eq_liftHomotopy_iff]
  exact and_iff_right fun a => H'.2.comp (.prodMk_left a)

Depends on / 依赖: DFunLike, DFunLike.coe_fn_eq, and_iff_right, coe_fn_eq, eq_liftHomotopy_iff, prodMk_left, simp_rw
-/
lemma eq_liftHomotopy_iff' (H' : C(I × A, E)) :
    H' = cov.liftHomotopy H f H_0 ↔ p ∘ H' = H ∧ forall a, H' (0, a) = f a := by
  simp_rw [← DFunLike.coe_fn_eq, eq_liftHomotopy_iff]
  exact and_iff_right fun a => H'.2.comp (.prodMk_left a)

variable {f₀ f₁ : C(A, X)} {S : Set A} (F : f₀.HomotopyRel f₁ S)

set_option backward.isDefEq.respectTransparency.types false in
open ContinuousMap in
/--
Definition of `liftHomotopyRel` / `liftHomotopyRel` 的定义

English:
definition liftHomotopyRel
  signature: [PreconnectedSpace A]
  body: have F_0 : forall a, F (0, a) = p (f₀' a) := fun a => (F.apply_zero a).trans (congr_fun h₀ a).symm
  have rel : forall t, forall a in S, cov.liftHomotopy F f₀' F_0 (t, a) = f₀' a := fun t a ha => by
    rw [liftHomotopy_apply]; rw [cov.const_of_comp (ContinuousMap.continuous _) _ t 0]
    · apply co

中文:
定义 liftHomotopyRel
  签名: [预连通空间 A]
  定义体: have F_0 : forall a, F (0, a) = p (f₀' a) := fun a => (F.apply_zero a).trans (congr_fun h₀ a).symm
  have rel : forall t, forall a in S, cov.liftHomotopy F f₀' F_0 (t, a) = f₀' a := fun t a ha => by
    rw [liftHomotopy_apply]; rw [cov.const_of_comp (ContinuousMap.continuous _) _ t 0]
    · apply co

Depends on / 依赖: ContinuousMap, ContinuousMap.continuous, F.apply_zero, F.prop, apply_zero, comp_apply, congr_fun, const_of_comp, continuous, cov.const_of_comp, cov.liftHomotopy, cov.liftHomotopy_zer, cov.liftPath_lifts, cov.liftPath_zero, liftHomotopy, liftHomotopy_apply, liftHomotopy_zer, liftPath_lifts, liftPath_zero, map_zero_left
-/
def liftHomotopyRel [PreconnectedSpace A]
    {f₀' f₁' : C(A, E)} (he : exists a in S, f₀' a = f₁' a)
    (h₀ : p ∘ f₀' = f₀) (h₁ : p ∘ f₁' = f₁) : f₀'.HomotopyRel f₁' S :=
  have F_0 : forall a, F (0, a) = p (f₀' a) := fun a => (F.apply_zero a).trans (congr_fun h₀ a).symm
  have rel : forall t, forall a in S, cov.liftHomotopy F f₀' F_0 (t, a) = f₀' a := fun t a ha => by
    rw [liftHomotopy_apply]; rw [cov.const_of_comp (ContinuousMap.continuous _) _ t 0]
    · apply cov.liftPath_zero
    · intro t t'; simp_rw [← p.comp_apply, cov.liftPath_lifts]
      exact (F.prop t a ha).trans (F.prop t' a ha).symm
  { toContinuousMap := cov.liftHomotopy F f₀' F_0
    map_zero_left := cov.liftHomotopy_zero F f₀' F_0
    map_one_left := by
      obtain ⟨a, ha, he⟩ := he
      simp_rw [toFun_eq_coe, ← ContinuousMap.curry_apply]
      refine congr_fun (cov.eq_of_comp_eq
(ContinuousMap.continuous _) f₁'.continuous ?_ a (rel 1 a ha).trans he)
      ext a; rw [h₁, Function.comp_apply, ContinuousMap.curry_apply]
      exact (congr_fun (cov.liftHomotopy_lifts F f₀' _) (1, a)).trans (F.apply_one a)
    prop' := rel }

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `homotopicRel_iff_comp` / 定理 `homotopicRel_iff_comp`

English:
theorem homotopicRel_iff_comp
  statement: [PreconnectedSpace A] {f₀ f₁ : C(A, E)} {S : Set A}
  proof: ⟨fun ⟨F⟩ => ⟨F.compContinuousMap _⟩, fun ⟨F⟩ => ⟨cov.liftHomotopyRel F he rfl rfl⟩⟩

中文:
定理 homotopicRel_iff_comp
  结论: [预连通空间 A] {f₀ f₁ : C(A, E)} {S : 集合 A}
  证明: ⟨fun ⟨F⟩ => ⟨F.compContinuousMap _⟩, fun ⟨F⟩ => ⟨cov.liftHomotopyRel F he rfl rfl⟩⟩

Depends on / 依赖: F.compContinuousMap, compContinuousMap, cov.liftHomotopyRel, liftHomotopyRel
-/
theorem homotopicRel_iff_comp [PreconnectedSpace A] {f₀ f₁ : C(A, E)} {S : Set A}
    (he : exists a in S, f₀ a = f₁ a) : f₀.HomotopicRel f₁ S ↔
      (ContinuousMap.comp ⟨p, cov.continuous⟩ f₀).HomotopicRel (.comp ⟨p, cov.continuous⟩ f₁) S :=
  ⟨fun ⟨F⟩ => ⟨F.compContinuousMap _⟩, fun ⟨F⟩ => ⟨cov.liftHomotopyRel F he rfl rfl⟩⟩

/--
theorem `homotopicRel_liftPath` / 定理 `homotopicRel_liftPath`

English:
theorem homotopicRel_liftPath
  statement: {γ₀ γ₁ : C(I, X)}
  proof: h.map fun H => cov.liftHomotopyRel (f₀' := cov.liftPath γ₀ e h₀) (f₁' := cov.liftPath γ₁ e h₁) H
    ⟨0, .inl rfl, by simp_rw [liftPath_zero]⟩ (liftPath_lifts ..) (liftPath_lifts ..)

中文:
定理 homotopicRel_liftPath
  结论: {γ₀ γ₁ : C(I, X)}
  证明: h.map fun H => cov.liftHomotopyRel (f₀' := cov.liftPath γ₀ e h₀) (f₁' := cov.liftPath γ₁ e h₁) H
    ⟨0, .inl rfl, by simp_rw [liftPath_zero]⟩ (liftPath_lifts ..) (liftPath_lifts ..)

Depends on / 依赖: cov.liftHomotopyRel, cov.liftPath, h.map, liftHomotopyRel, liftPath, liftPath_lifts, liftPath_zero, simp_rw
-/
theorem homotopicRel_liftPath {γ₀ γ₁ : C(I, X)}
    (h : γ₀.HomotopicRel γ₁ {0,1}) (e : E) (h₀ : γ₀ 0 = p e) (h₁ : γ₁ 0 = p e) :
    (cov.liftPath γ₀ e h₀).HomotopicRel (cov.liftPath γ₁ e h₁) {0,1} :=
  h.map fun H => cov.liftHomotopyRel (f₀' := cov.liftPath γ₀ e h₀) (f₁' := cov.liftPath γ₁ e h₁) H
    ⟨0, .inl rfl, by simp_rw [liftPath_zero]⟩ (liftPath_lifts ..) (liftPath_lifts ..)

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `liftPath_apply_one_eq_of_homotopicRel` / 定理 `liftPath_apply_one_eq_of_homotopicRel`

English:
theorem liftPath_apply_one_eq_of_homotopicRel
  statement: {γ₀ γ₁ : C(I, X)}
  proof: by
  have := (cov.homotopicRel_liftPath h e h₀ h₁).some
  rw [← this.eq_fst 0 (.inr rfl)]; rw [← this.eq_snd 0 (.inr rfl)]

中文:
定理 liftPath_apply_one_eq_of_homotopicRel
  结论: {γ₀ γ₁ : C(I, X)}
  证明: by
  have := (cov.homotopicRel_liftPath h e h₀ h₁).some
  rw [← this.eq_fst 0 (.inr rfl)]; rw [← this.eq_snd 0 (.inr rfl)]

Depends on / 依赖: cov.homotopicRel_liftPath, eq_fst, eq_snd, homotopicRel_liftPath, this.eq_fst, this.eq_snd
-/
theorem liftPath_apply_one_eq_of_homotopicRel {γ₀ γ₁ : C(I, X)}
    (h : γ₀.HomotopicRel γ₁ {0,1}) (e : E) (h₀ : γ₀ 0 = p e) (h₁ : γ₁ 0 = p e) :
    cov.liftPath γ₀ e h₀ 1 = cov.liftPath γ₁ e h₁ 1 := by
  have := (cov.homotopicRel_liftPath h e h₀ h₁).some
  rw [← this.eq_fst 0 (.inr rfl)]; rw [← this.eq_snd 0 (.inr rfl)]

/--
Definition of `monodromy` / `monodromy` 的定义

English:
definition monodromy
  signature: {x y : X} (γ : Path.Homotopic.Quotient x y)
  body: fun e => γ.lift (fun γ : Path x y => ⟨cov.liftPath γ e (γ.source.trans e.2.symm) 1,
      congr($(cov.liftPath_lifts ..) 1).trans γ.target⟩)
    fun _ _ h => Subtype.ext (cov.liftPath_apply_one_eq_of_homotopicRel h ..)

中文:
定义 monodromy
  签名: {x y : X} (γ : 道路.同伦.商 x y)
  定义体: fun e => γ.lift (fun γ : Path x y => ⟨cov.liftPath γ e (γ.source.trans e.2.symm) 1,
      congr($(cov.liftPath_lifts ..) 1).trans γ.target⟩)
    fun _ _ h => Subtype.ext (cov.liftPath_apply_one_eq_of_homotopicRel h ..)

Depends on / 依赖: Subtype, Subtype.ext, cov.liftPath, cov.liftPath_apply_one_eq_of_homotopicRel, cov.liftPath_lifts, liftPath, liftPath_apply_one_eq_of_homotopicRel, liftPath_lifts, source, source.trans, target
-/
def monodromy {x y : X} (γ : Path.Homotopic.Quotient x y) :
    p ⁻¹' {x} -> p ⁻¹' {y} :=
  fun e => γ.lift (fun γ : Path x y => ⟨cov.liftPath γ e (γ.source.trans e.2.symm) 1,
      congr($(cov.liftPath_lifts ..) 1).trans γ.target⟩)
    fun _ _ h => Subtype.ext (cov.liftPath_apply_one_eq_of_homotopicRel h ..)

/--
Definition of `liftPathQuotient` / `liftPathQuotient` 的定义

English:
definition liftPathQuotient
  signature: {x y : X} (γ : Path.Homotopic.Quotient x y) (e : p ⁻¹' {x})
  body: have he (γ : Path x y) : γ 0 = p (e : E) := by aesop
  let g (γ : Path x y) : Path.Homotopic.Quotient (e : E) (cov.liftPath γ (e : E) (he γ) 1) :=
    .mk ⟨cov.liftPath γ (e : E) (he γ), cov.liftPath_zero .., rfl⟩
  let _i : Setoid (Path x y) := Path.Homotopic.setoid x y
  have hg (γ γ' : Path x y) 

中文:
定义 liftPathQuotient
  签名: {x y : X} (γ : 道路.同伦.商 x y) (e : p ⁻¹' {x})
  定义体: have he (γ : Path x y) : γ 0 = p (e : E) := by aesop
  let g (γ : Path x y) : Path.Homotopic.Quotient (e : E) (cov.liftPath γ (e : E) (he γ) 1) :=
    .mk ⟨cov.liftPath γ (e : E) (he γ), cov.liftPath_zero .., rfl⟩
  let _i : Setoid (Path x y) := Path.Homotopic.setoid x y
  have hg (γ γ' : Path x y) 

Depends on / 依赖: Homotopic, Path.Ho, Path.Homotopic.Quotient, Path.Homotopic.Quotient.cast_heq, Path.Homotopic.Quotient.mk_cast, Path.Homotopic.setoid, Quotient, Setoid, cast_heq, cov.liftPath, cov.liftPath_apply_one_eq_of_homotopicRel, cov.liftPath_zero, heq_of_eq, liftPath, liftPath_apply_one_eq_of_homotopicRel, liftPath_zero, mk_cast, setoid
-/
def liftPathQuotient {x y : X} (γ : Path.Homotopic.Quotient x y) (e : p ⁻¹' {x}) :
    Path.Homotopic.Quotient e.1 (cov.monodromy γ e) :=
  have he (γ : Path x y) : γ 0 = p (e : E) := by aesop
  let g (γ : Path x y) : Path.Homotopic.Quotient (e : E) (cov.liftPath γ (e : E) (he γ) 1) :=
    .mk ⟨cov.liftPath γ (e : E) (he γ), cov.liftPath_zero .., rfl⟩
  let _i : Setoid (Path x y) := Path.Homotopic.setoid x y
  have hg (γ γ' : Path x y) (hγ : γ ≈ γ') : g γ ≍ g γ' := by
    refine .trans (heq_of_eq ?_) (Path.Homotopic.Quotient.cast_heq rfl
      (cov.liftPath_apply_one_eq_of_homotopicRel hγ _ (he γ) _))
    rw [← Path.Homotopic.Quotient.mk_cast]; rw [Path.Homotopic.Quotient.eq]
    exact cov.homotopicRel_liftPath hγ _ (by aesop) (by aesop)
  γ.hrecOn g hg

/--
theorem `map_liftPathQuotient` / 定理 `map_liftPathQuotient`

English:
theorem map_liftPathQuotient
  given: {x y : X} (γ : Path.Homotopic.Quotient x y) (e : p ⁻¹' {x})
  proof: by
  obtain ⟨γ⟩ := γ
  refine congr_arg Path.Homotopic.Quotient.mk ?_
  ext1
  exact cov.liftPath_lifts _ _ (γ.source.trans e.2.symm)

中文:
定理 map_liftPathQuotient
  条件: {x y : X} (γ : 道路.同伦.商 x y) (e : p ⁻¹' {x})
  证明: by
  obtain ⟨γ⟩ := γ
  refine congr_arg Path.Homotopic.Quotient.mk ?_
  ext1
  exact cov.liftPath_lifts _ _ (γ.source.trans e.2.symm)

Depends on / 依赖: Homotopic, Path.Homotopic.Quotient.mk, Quotient, congr_arg, cov.liftPath_lifts, liftPath_lifts, source, source.trans
-/
theorem map_liftPathQuotient {x y : X} (γ : Path.Homotopic.Quotient x y) (e : p ⁻¹' {x}) :
    (cov.liftPathQuotient γ e).map ⟨p, cov.continuous⟩ = γ.cast e.2 (cov.monodromy γ e).2 := by
  obtain ⟨γ⟩ := γ
  refine congr_arg Path.Homotopic.Quotient.mk ?_
  ext1
  exact cov.liftPath_lifts _ _ (γ.source.trans e.2.symm)

/--
theorem `monodromy_map` / 定理 `monodromy_map`

English:
theorem monodromy_map
  given: {x y : E} (γ : Path.Homotopic.Quotient x y)
  proof: Subtype.ext by
  obtain ⟨γ⟩ := γ
  exact congr($((cov.eq_liftPath_iff' _).mpr ⟨rfl, γ.source⟩) 1).symm.trans γ.target

中文:
定理 monodromy_map
  条件: {x y : E} (γ : 道路.同伦.商 x y)
  证明: Subtype.ext by
  obtain ⟨γ⟩ := γ
  exact congr($((cov.eq_liftPath_iff' _).mpr ⟨rfl, γ.source⟩) 1).symm.trans γ.target

Depends on / 依赖: Subtype, Subtype.ext, cov.eq_liftPath_iff, eq_liftPath_iff, source, symm.trans, target
-/
theorem monodromy_map {x y : E} (γ : Path.Homotopic.Quotient x y) :
cov.monodromy (γ.map ⟨p, cov.continuous⟩) ⟨x, rfl⟩ = ⟨y, rfl⟩ := Subtype.ext by
  obtain ⟨γ⟩ := γ
  exact congr($((cov.eq_liftPath_iff' _).mpr ⟨rfl, γ.source⟩) 1).symm.trans γ.target

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `monodromy_eq_of_map_eq` / 定理 `monodromy_eq_of_map_eq`

English:
theorem monodromy_eq_of_map_eq
  statement: {x y : X} {γ : Path.Homotopic.Quotient x y}
  proof: by
  convert ← cov.monodromy_map Γ
  exacts [ey.2, ex.2, ey.2, by rw [eq]; exact γ.cast_heq .., ey.2]

中文:
定理 monodromy_eq_of_map_eq
  结论: {x y : X} {γ : 道路.同伦.商 x y}
  证明: by
  convert ← cov.monodromy_map Γ
  exacts [ey.2, ex.2, ey.2, by rw [eq]; exact γ.cast_heq .., ey.2]

Depends on / 依赖: cast_heq, convert, cov.monodromy_map, exacts, monodromy_map
-/
theorem monodromy_eq_of_map_eq {x y : X} {γ : Path.Homotopic.Quotient x y}
    {ex : p ⁻¹' {x}} {ey : p ⁻¹' {y}} (Γ : Path.Homotopic.Quotient ex.1 ey)
    (eq : Γ.map ⟨p, cov.continuous⟩ = γ.cast ex.2 ey.2) :
    cov.monodromy γ ex = ey := by
  convert ← cov.monodromy_map Γ
  exacts [ey.2, ex.2, ey.2, by rw [eq]; exact γ.cast_heq .., ey.2]

/--
theorem `monodromy_refl` / 定理 `monodromy_refl`

English:
theorem monodromy_refl
  given: {x : X}
  statement: cov.monodromy (.refl x) = id
  proof: funext fun e => Subtype.ext congr($(cov.liftPath_const e.2.symm) 1)

中文:
定理 monodromy_refl
  条件: {x : X}
  结论: cov.monodromy (.refl x) = id
  证明: funext fun e => Subtype.ext congr($(cov.liftPath_const e.2.symm) 1)

Depends on / 依赖: Subtype, Subtype.ext, cov.liftPath_const, liftPath_const
-/
theorem monodromy_refl {x : X} : cov.monodromy (.refl x) = id :=
  funext fun e => Subtype.ext congr($(cov.liftPath_const e.2.symm) 1)

/--
theorem `monodromy_trans_apply` / 定理 `monodromy_trans_apply`

English:
theorem monodromy_trans_apply
  statement: {x y z : X}
  proof: by
  obtain ⟨γ⟩ := γ; obtain ⟨γ'⟩ := γ'
  exact Subtype.ext (congr($(cov.liftPath_trans e.2.symm ..) 1).trans (Path.target _))

中文:
定理 monodromy_trans_apply
  结论: {x y z : X}
  证明: by
  obtain ⟨γ⟩ := γ; obtain ⟨γ'⟩ := γ'
  exact Subtype.ext (congr($(cov.liftPath_trans e.2.symm ..) 1).trans (Path.target _))

Depends on / 依赖: Path.target, Subtype, Subtype.ext, cov.liftPath_trans, liftPath_trans, target
-/
theorem monodromy_trans_apply {x y z : X}
    (γ : Path.Homotopic.Quotient x y) (γ' : Path.Homotopic.Quotient y z) (e) :
    cov.monodromy (γ.trans γ') e = cov.monodromy γ' (cov.monodromy γ e) := by
  obtain ⟨γ⟩ := γ; obtain ⟨γ'⟩ := γ'
  exact Subtype.ext (congr($(cov.liftPath_trans e.2.symm ..) 1).trans (Path.target _))

/--
Definition of `fundamentalGroupMulAction` / `fundamentalGroupMulAction` 的定义

English:
definition fundamentalGroupMulAction
  signature: (x : X)
  body: { smul := cov.monodromy (x := x) (y := x)
    mul_smul _ _ _ := cov.monodromy_trans_apply ..
    one_smul := congr_fun cov.monodromy_refl }

中文:
定义 fundamentalGroupMulAction
  签名: (x : X)
  定义体: { smul := cov.monodromy (x := x) (y := x)
    mul_smul _ _ _ := cov.monodromy_trans_apply ..
    one_smul := congr_fun cov.monodromy_refl }
-/
@[reducible] def fundamentalGroupMulAction (x : X) :
    MulAction (FundamentalGroup X x) (p ⁻¹' {x}) :=
  { smul := cov.monodromy (x := x) (y := x)
    mul_smul _ _ _ := cov.monodromy_trans_apply ..
    one_smul := congr_fun cov.monodromy_refl }

/--
Definition of `monodromyPerm` / `monodromyPerm` 的定义

English:
definition monodromyPerm
  signature: (x : X)
  body: letI := cov.fundamentalGroupMulAction x
  MulAction.toPermHom _ _

中文:
定义 monodromyPerm
  签名: (x : X)
  定义体: letI := cov.fundamentalGroupMulAction x
  MulAction.toPermHom _ _

Depends on / 依赖: MulAction, MulAction.toPermHom, cov.fundamentalGroupMulAction, fundamentalGroupMulAction, toPermHom
-/
def monodromyPerm (x : X) : FundamentalGroup X x ->* Equiv.Perm (p ⁻¹' {x}) :=
  letI := cov.fundamentalGroupMulAction x
  MulAction.toPermHom _ _

/--
theorem `coe_monodromyPerm` / 定理 `coe_monodromyPerm`

English:
theorem coe_monodromyPerm
  given: {x γ}
  statement: cov.monodromyPerm x γ = cov.monodromy γ
  proof: rfl

中文:
定理 coe_monodromyPerm
  条件: {x γ}
  结论: cov.monodromyPerm x γ = cov.monodromy γ
  证明: rfl
-/
@[simp] theorem coe_monodromyPerm {x γ} : cov.monodromyPerm x γ = cov.monodromy γ := rfl

open CategoryTheory

/--
Definition of `monodromyFunctor` / `monodromyFunctor` 的定义

English:
definition monodromyFunctor
  signature: : FundamentalGroupoid X ⥤ Type _ where
  body: p ⁻¹' {x.as}
  map f := ↾(cov.monodromy f)
  map_id _ := by ext x : 3; simpa using! congr_fun cov.monodromy_refl x
  map_comp _ _ := by ext : 3; simpa using! cov.monodromy_trans_apply _ _ _

中文:
定义 monodromyFunctor
  签名: : FundamentalGroupoid X ⥤ 类型 _ where
  定义体: p ⁻¹' {x.as}
  map f := ↾(cov.monodromy f)
  map_id _ := by ext x : 3; simpa using! congr_fun cov.monodromy_refl x
  map_comp _ _ := by ext : 3; simpa using! cov.monodromy_trans_apply _ _ _
-/
@[simps] def monodromyFunctor : FundamentalGroupoid X ⥤ Type _ where
  obj x := p ⁻¹' {x.as}
  map f := ↾(cov.monodromy f)
  map_id _ := by ext x : 3; simpa using! congr_fun cov.monodromy_refl x
  map_comp _ _ := by ext : 3; simpa using! cov.monodromy_trans_apply _ _ _

/--
theorem `monodromy_bijective` / 定理 `monodromy_bijective`

English:
theorem monodromy_bijective
  given: {x y : X} (γ : Path.Homotopic.Quotient x y)
  proof: (isIso_iff_bijective _).mp (cov.monodromyFunctor.map_isIso _)

中文:
定理 monodromy_bijective
  条件: {x y : X} (γ : 道路.同伦.商 x y)
  证明: (isIso_iff_bijective _).mp (cov.monodromyFunctor.map_isIso _)

Depends on / 依赖: cov.monodromyFunctor.map_isIso, isIso_iff_bijective, map_isIso, monodromyFunctor
-/
theorem monodromy_bijective {x y : X} (γ : Path.Homotopic.Quotient x y) :
    (cov.monodromy γ).Bijective :=
  (isIso_iff_bijective _).mp (cov.monodromyFunctor.map_isIso _)

/--
lemma `injective_path_homotopic_map` / 引理 `injective_path_homotopic_map`

English:
lemma injective_path_homotopic_map
  given: (e₀ e₁ : E)
  proof: by
  refine Quotient.ind₂ fun γ₀ γ₁ => ?_
  dsimp only
  simp only [Path.Homotopic.Quotient.mk''_eq_mk]
  simp_rw [← Path.Homotopic.Quotient.mk_map]
  iterate 2 rw [Path.Homotopic.Quotient.eq]
  exact (cov.homotopicRel_iff_comp ⟨0, .inl rfl, γ₀.source.trans γ₁.source.symm⟩).mpr

中文:
引理 injective_path_homotopic_map
  条件: (e₀ e₁ : E)
  证明: by
  refine Quotient.ind₂ fun γ₀ γ₁ => ?_
  dsimp only
  simp only [Path.Homotopic.Quotient.mk''_eq_mk]
  simp_rw [← Path.Homotopic.Quotient.mk_map]
  iterate 2 rw [Path.Homotopic.Quotient.eq]
  exact (cov.homotopicRel_iff_comp ⟨0, .inl rfl, γ₀.source.trans γ₁.source.symm⟩).mpr

Depends on / 依赖: Homotopic, Path.Homotopic.Quotient.eq, Path.Homotopic.Quotient.mk, Path.Homotopic.Quotient.mk_map, Quotient, Quotient.ind, _eq_mk, cov.homotopicRel_iff_comp, homotopicRel_iff_comp, iterate, mk_map, simp_rw, source, source.symm, source.trans
-/
lemma injective_path_homotopic_map (e₀ e₁ : E) :
    Injective fun γ : Path.Homotopic.Quotient e₀ e₁ => γ.map ⟨p, cov.continuous⟩ := by
  refine Quotient.ind₂ fun γ₀ γ₁ => ?_
  dsimp only
  simp only [Path.Homotopic.Quotient.mk''_eq_mk]
  simp_rw [← Path.Homotopic.Quotient.mk_map]
  iterate 2 rw [Path.Homotopic.Quotient.eq]
  exact (cov.homotopicRel_iff_comp ⟨0, .inl rfl, γ₀.source.trans γ₁.source.symm⟩).mpr

/--
theorem `existsUnique_continuousMap_lifts` / 定理 `existsUnique_continuousMap_lifts`

English:
theorem existsUnique_continuousMap_lifts
  statement: [SimplyConnectedSpace A] [LocallyPathConnectedSpace A]
  proof: by
  refine cov.isLocalHomeomorph.existsUnique_continuousMap_lifts f a₀ e₀ he (fun γ γ_0 => ?_)
    fun γ γ' Γ Γ' γ_0 γ'_0 Γ_0 Γ'_0 Γ_lifts Γ'_lifts γγ'1 => ?_
  · simpa [and_comm] using cov.exists_path_lifts (f.comp γ) e₀ (by simp [γ_0, he])
  let pγ : Path a₀ (γ 1) := ⟨γ, γ_0, rfl⟩
  let pγ' : Pat

中文:
定理 存在Unique_continuousMap_lifts
  结论: [单连通空间 A] [LocallyPathConnected空间 A]
  证明: by
  refine cov.isLocalHomeomorph.existsUnique_continuousMap_lifts f a₀ e₀ he (fun γ γ_0 => ?_)
    fun γ γ' Γ Γ' γ_0 γ'_0 Γ_0 Γ'_0 Γ_lifts Γ'_lifts γγ'1 => ?_
  · simpa [and_comm] using cov.exists_path_lifts (f.comp γ) e₀ (by simp [γ_0, he])
  let pγ : Path a₀ (γ 1) := ⟨γ, γ_0, rfl⟩
  let pγ' : Pat

Depends on / 依赖: ContinuousMap, ContinuousMap.HomotopicRel.comp_continuousMap, HomotopicRel, SimplyConnectedSpace, SimplyConnectedSpace.paths_homotopic, _lifts, and_comm, comp_continuousMap, convert, cov.exists_path_lifts, cov.isLocalHomeomorph.existsUnique_continuousMap_lifts, cov.liftPath_apply_one_eq_of_homotopicRel, existsUnique_continuousMap_lifts, exists_path_lifts, f.comp, isLocalHomeomorph, liftPath_apply_one_eq_of_homotopicRel, paths_homotopic
-/
theorem existsUnique_continuousMap_lifts [SimplyConnectedSpace A] [LocallyPathConnectedSpace A]
    (f : C(A, X)) (a₀ : A) (e₀ : E) (he : p e₀ = f a₀) :
    exists! F : C(A, E), F a₀ = e₀ ∧ p ∘ F = f := by
  refine cov.isLocalHomeomorph.existsUnique_continuousMap_lifts f a₀ e₀ he (fun γ γ_0 => ?_)
    fun γ γ' Γ Γ' γ_0 γ'_0 Γ_0 Γ'_0 Γ_lifts Γ'_lifts γγ'1 => ?_
  · simpa [and_comm] using cov.exists_path_lifts (f.comp γ) e₀ (by simp [γ_0, he])
  let pγ : Path a₀ (γ 1) := ⟨γ, γ_0, rfl⟩
  let pγ' : Path a₀ (γ 1) := ⟨γ', γ'_0, γγ'1.symm⟩
  convert!
    cov.liftPath_apply_one_eq_of_homotopicRel
      (ContinuousMap.HomotopicRel.comp_continuousMap (SimplyConnectedSpace.paths_homotopic pγ pγ')
        f)
      e₀ (by simp [he]) (by simp [he]) <;>
    rw [eq_liftPath_iff']
  exacts [⟨Γ_lifts, Γ_0⟩, ⟨Γ'_lifts, Γ'_0⟩]

set_option backward.isDefEq.respectTransparency.types false in
open FundamentalGroup Path.Homotopic.Quotient in
/--
theorem `existsUnique_continuousMap_lifts_of_range_le` / 定理 `existsUnique_continuousMap_lifts_of_range_le`

English:
theorem existsUnique_continuousMap_lifts_of_range_le
  proof: by
  refine cov.isLocalHomeomorph.existsUnique_continuousMap_lifts f a₀ e₀ he (fun γ γ_0 => ?_)
    fun γ γ' Γ Γ' γ_0 γ'_0 Γ_0 Γ'_0 Γ_lifts Γ'_lifts γγ'1 => ?_
  · simpa [and_comm] using cov.exists_path_lifts (f.comp γ) e₀ (by simp [γ_0, he])
  rw [(cov.eq_liftPath_iff' <| by simp [γ_0]; rw [he]).mp

中文:
定理 存在Unique_continuousMap_lifts_of_range_le
  证明: by
  refine cov.isLocalHomeomorph.existsUnique_continuousMap_lifts f a₀ e₀ he (fun γ γ_0 => ?_)
    fun γ γ' Γ Γ' γ_0 γ'_0 Γ_0 Γ'_0 Γ_lifts Γ'_lifts γγ'1 => ?_
  · simpa [and_comm] using cov.exists_path_lifts (f.comp γ) e₀ (by simp [γ_0, he])
  rw [(cov.eq_liftPath_iff' <| by simp [γ_0]; rw [he]).mp

Depends on / 依赖: _lifts, and_comm, cov.eq_liftPath_iff, cov.exists_path_lifts, cov.isLocalHomeomorph.existsUnique_continuousMap_lifts, cov.monodromy, eq_liftPath_iff, existsUnique_continuousMap_lifts, exists_path_lifts, f.comp, isLocalHomeomorph, monodromy
-/
theorem existsUnique_continuousMap_lifts_of_range_le
    [PathConnectedSpace A] [LocallyPathConnectedSpace A]
    {f : C(A, X)} {a₀ : A} {e₀ : E} (he : p e₀ = f a₀)
    (le : (map f a₀).range <= (mapOfEq ⟨p, cov.continuous⟩ he).range) :
    exists! F : C(A, E), F a₀ = e₀ ∧ p ∘ F = f := by
  refine cov.isLocalHomeomorph.existsUnique_continuousMap_lifts f a₀ e₀ he (fun γ γ_0 => ?_)
    fun γ γ' Γ Γ' γ_0 γ'_0 Γ_0 Γ'_0 Γ_lifts Γ'_lifts γγ'1 => ?_
  · simpa [and_comm] using cov.exists_path_lifts (f.comp γ) e₀ (by simp [γ_0, he])
  rw [(cov.eq_liftPath_iff' <| by simp [γ_0]; rw [he]).mpr ⟨Γ_lifts, Γ_0⟩,
    (cov.eq_liftPath_iff' <| by simp [γ'_0, he]).mpr ⟨Γ'_lifts, Γ'_0⟩]
  let pγ : Path a₀ (γ 1) := ⟨γ, γ_0, rfl⟩
  let pγ' : Path a₀ (γ 1) := ⟨γ', γ'_0, γγ'1.symm⟩
  change (cov.monodromy (.mk <| pγ.map f.continuous) ⟨e₀, he⟩).1 =
    (cov.monodromy (.mk <| pγ'.map f.continuous) ⟨e₀, he⟩).1
  rw [← Subtype.ext_iff]
  apply (cov.monodromy_bijective <| .mk (pγ'.map f.continuous).symm).1
  simp_rw [← monodromy_trans_apply, ← mk_trans]
  conv_rhs => rw [← eq.2 ⟨.reflTransSymm _⟩, mk_refl, monodromy_refl]
  rw [Path.map_symm]; rw [← Path.map_trans]
  set pγγ' : Path a₀ a₀ := pγ.trans pγ'.symm
  obtain ⟨⟨pΓΓ'⟩, eq⟩ := le ⟨fromPath (.mk pγγ'), rfl⟩
  rw [mapOfEq_apply]; rw [map_apply]; rw [← mk_map] at eq
  exact eq ▸ Subtype.ext congr($(cov.monodromy_map <| .mk _))

end homotopy_lifting

end IsCoveringMap

/--
theorem `IsCoveringMapOn.existsUnique_continuousMap_lifts` / 定理 `IsCoveringMapOn.existsUnique_continuousMap_lifts`

English:
theorem IsCoveringMapOn.existsUnique_continuousMap_lifts
  statement: [SimplyConnectedSpace A]
  proof: by
  obtain ⟨f, rfl⟩ : exists f' : C(A, s), f = .comp ⟨Subtype.val, by fun_prop⟩ f' :=
    ⟨⟨fun a => ⟨f a, hs a⟩, by fun_prop⟩, rfl⟩
  lift e₀ to p ⁻¹' s using by rw [Set.mem_preimage, he]; apply hs
  rcases cov.isCoveringMap_restrictPreimage.existsUnique_continuousMap_lifts f a₀ e₀
    (Subtype.ex

中文:
定理 IsCoveringMapOn.存在Unique_continuousMap_lifts
  结论: [单连通空间 A]
  证明: by
  obtain ⟨f, rfl⟩ : exists f' : C(A, s), f = .comp ⟨Subtype.val, by fun_prop⟩ f' :=
    ⟨⟨fun a => ⟨f a, hs a⟩, by fun_prop⟩, rfl⟩
  lift e₀ to p ⁻¹' s using by rw [Set.mem_preimage, he]; apply hs
  rcases cov.isCoveringMap_restrictPreimage.existsUnique_continuousMap_lifts f a₀ e₀
    (Subtype.ex

Depends on / 依赖: ContinuousMap, ContinuousMap.coe_comp, ContinuousMap.coe_mk, Function, Function.comp_def, Set.mem_preimage, Subtype, Subtype.ext, Subtype.val, coe_comp, coe_mk, comp_def, cov.isCoveringMap_restrictPreimage.existsUnique_continuousMap_lifts, existsUnique_continuousMap_lifts, fun_prop, hF_unique, isCoveringMap_restrictPreimage, mem_preimage
-/
theorem IsCoveringMapOn.existsUnique_continuousMap_lifts [SimplyConnectedSpace A]
    [LocallyPathConnectedSpace A] {s : Set X} (cov : IsCoveringMapOn p s) (f : C(A, X)) {a₀ : A}
    {e₀ : E} (he : p e₀ = f a₀) (hs : forall a, f a in s) :
    exists! F : C(A, E), F a₀ = e₀ ∧ p ∘ F = f := by
  obtain ⟨f, rfl⟩ : exists f' : C(A, s), f = .comp ⟨Subtype.val, by fun_prop⟩ f' :=
    ⟨⟨fun a => ⟨f a, hs a⟩, by fun_prop⟩, rfl⟩
  lift e₀ to p ⁻¹' s using by rw [Set.mem_preimage, he]; apply hs
  rcases cov.isCoveringMap_restrictPreimage.existsUnique_continuousMap_lifts f a₀ e₀
    (Subtype.ext he) with ⟨F, ⟨rfl, hF⟩, hF_unique⟩
  refine ⟨.comp ⟨Subtype.val, by fun_prop⟩ F, ⟨rfl, ?_⟩, ?_⟩
  · simp [← hF, Function.comp_def]
  · rintro F' ⟨hF'₁, hF'₂⟩
    simp only [ContinuousMap.coe_comp, ContinuousMap.coe_mk, funext_iff,
      Function.comp_apply] at hF'₂
    specialize hF_unique
      ⟨fun a => ⟨F' a, by rw [Set.mem_preimage, hF'₂]; exact (f a).2⟩, by fun_prop⟩
      ⟨Subtype.ext hF'₁, ?_⟩
    · ext; simp [← hF'₂]
    · ext; simp [← hF_unique]

namespace IsQuotientCoveringMap

variable {G : Type*} [Group G] [MulAction G E] (hp : IsQuotientCoveringMap p G) {g : G}

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `monodromy_toPermFiber` / 定理 `monodromy_toPermFiber`

English:
theorem monodromy_toPermFiber
  given: {x y : X} {γ : Path.Homotopic.Quotient x y} {e : p ⁻¹' {x}}
  proof: hp.isCoveringMap.monodromy
    monodromy γ (hp.toPermFiber x g e) = hp.toPermFiber y g (monodromy γ e) :=
  let Γ := hp.isCoveringMap.liftPathQuotient γ e
  let g' : C(E, E) := ⟨_, hp.toContinuousConstSMul.continuous_const_smul g⟩
  let p' : C(E, X) := ⟨p, hp.continuous⟩
  have hgp : p'.comp g' = p'

中文:
定理 monodromy_toPermFiber
  条件: {x y : X} {γ : 道路.同伦.商 x y} {e : p ⁻¹' {x}}
  证明: hp.isCoveringMap.monodromy
    monodromy γ (hp.toPermFiber x g e) = hp.toPermFiber y g (monodromy γ e) :=
  let Γ := hp.isCoveringMap.liftPathQuotient γ e
  let g' : C(E, E) := ⟨_, hp.toContinuousConstSMul.continuous_const_smul g⟩
  let p' : C(E, X) := ⟨p, hp.continuous⟩
  have hgp : p'.comp g' = p'

Depends on / 依赖: hp.isCoveringMap.monodromy, isCoveringMap, monodromy
-/
theorem monodromy_toPermFiber {x y : X} {γ : Path.Homotopic.Quotient x y} {e : p ⁻¹' {x}} :
    letI monodromy := hp.isCoveringMap.monodromy
    monodromy γ (hp.toPermFiber x g e) = hp.toPermFiber y g (monodromy γ e) :=
  let Γ := hp.isCoveringMap.liftPathQuotient γ e
  let g' : C(E, E) := ⟨_, hp.toContinuousConstSMul.continuous_const_smul g⟩
  let p' : C(E, X) := ⟨p, hp.continuous⟩
  have hgp : p'.comp g' = p' := by ext; simp [g', p', hp.map_smul]
hp.isCoveringMap.monodromy_eq_of_map_eq (Γ.map g') show (Γ.map g').map p' = _ by
    rw [← Path.Homotopic.Quotient.map_comp]
    convert hp.isCoveringMap.map_liftPathQuotient γ e using 2
    · simp [g', p', hp.map_smul]
    · simp [g', p', hp.map_smul]
    · grind

/--
theorem `commute_monodromyPerm_toPermFiber` / 定理 `commute_monodromyPerm_toPermFiber`

English:
theorem commute_monodromyPerm_toPermFiber
  given: {x : X} {γ : FundamentalGroup X x}
  proof: by
  ext; exact congr($hp.monodromy_toPermFiber)

中文:
定理 commute_monodromyPerm_toPermFiber
  条件: {x : X} {γ : 基本群 X x}
  证明: by
  ext; exact congr($hp.monodromy_toPermFiber)

Depends on / 依赖: hp.monodromy_toPermFiber, monodromy_toPermFiber
-/
theorem commute_monodromyPerm_toPermFiber {x : X} {γ : FundamentalGroup X x} :
    Commute (hp.isCoveringMap.monodromyPerm x γ) (hp.toPermFiber x g) := by
  ext; exact congr($hp.monodromy_toPermFiber)

/--
theorem `monodromy_ext_iff` / 定理 `monodromy_ext_iff`

English:
theorem monodromy_ext_iff
  given: {x y : X} {γ γ' : Path.Homotopic.Quotient x y} (e : p ⁻¹' {x})
  proof: hp.isCoveringMap.monodromy
    monodromy γ e = monodromy γ' e ↔ monodromy γ = monodromy γ' where
  mp eq := by
    ext e'
    obtain ⟨g, rfl⟩ := hp.exists_toPermFiber_eq e e'
    simp_rw [monodromy_toPermFiber, eq]
  mpr := (congr_fun · _)

alias ⟨monodromy_ext, _⟩ := monodromy_ext_iff

中文:
定理 monodromy_ext_iff
  条件: {x y : X} {γ γ' : 道路.同伦.商 x y} (e : p ⁻¹' {x})
  证明: hp.isCoveringMap.monodromy
    monodromy γ e = monodromy γ' e ↔ monodromy γ = monodromy γ' where
  mp eq := by
    ext e'
    obtain ⟨g, rfl⟩ := hp.exists_toPermFiber_eq e e'
    simp_rw [monodromy_toPermFiber, eq]
  mpr := (congr_fun · _)

alias ⟨monodromy_ext, _⟩ := monodromy_ext_iff

Depends on / 依赖: hp.isCoveringMap.monodromy, isCoveringMap, monodromy
-/
theorem monodromy_ext_iff {x y : X} {γ γ' : Path.Homotopic.Quotient x y} (e : p ⁻¹' {x}) :
    letI monodromy := hp.isCoveringMap.monodromy
    monodromy γ e = monodromy γ' e ↔ monodromy γ = monodromy γ' where
  mp eq := by
    ext e'
    obtain ⟨g, rfl⟩ := hp.exists_toPermFiber_eq e e'
    simp_rw [monodromy_toPermFiber, eq]
  mpr := (congr_fun · _)

alias ⟨monodromy_ext, _⟩ := monodromy_ext_iff

variable {x : X} (e : p ⁻¹' {x}) {γ : FundamentalGroup X x}

/--
theorem `monodromy_eq_id_iff` / 定理 `monodromy_eq_id_iff`

English:
theorem monodromy_eq_id_iff
  proof: (congr_fun · _)
  mpr eq := (hp.monodromy_ext e (eq.trans congr($hp.isCoveringMap.monodromy_refl e).symm)).trans
    hp.isCoveringMap.monodromy_refl

中文:
定理 monodromy_eq_id_iff
  证明: (congr_fun · _)
  mpr eq := (hp.monodromy_ext e (eq.trans congr($hp.isCoveringMap.monodromy_refl e).symm)).trans
    hp.isCoveringMap.monodromy_refl

Depends on / 依赖: congr_fun
-/
theorem monodromy_eq_id_iff :
    hp.isCoveringMap.monodromy γ = id ↔ hp.isCoveringMap.monodromy γ e = e where
  mp := (congr_fun · _)
  mpr eq := (hp.monodromy_ext e (eq.trans congr($hp.isCoveringMap.monodromy_refl e).symm)).trans
    hp.isCoveringMap.monodromy_refl

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `ker_monodromyPerm` / 定理 `ker_monodromyPerm`

English:
theorem ker_monodromyPerm
  proof: by
  ext γ; constructor <;> intro h
  · refine ⟨(hp.isCoveringMap.liftPathQuotient γ e).cast rfl congr($h.symm e), ?_⟩
    rw [FundamentalGroup.mapOfEq_apply]; rw [Path.Homotopic.Quotient.map_cast]; rw [IsCoveringMap.map_liftPathQuotient]
    aesop
  · obtain ⟨γ, rfl⟩ := h
refine DFunLike.ext'
(hp.m

中文:
定理 ker_monodromyPerm
  证明: by
  ext γ; constructor <;> intro h
  · refine ⟨(hp.isCoveringMap.liftPathQuotient γ e).cast rfl congr($h.symm e), ?_⟩
    rw [FundamentalGroup.mapOfEq_apply]; rw [Path.Homotopic.Quotient.map_cast]; rw [IsCoveringMap.map_liftPathQuotient]
    aesop
  · obtain ⟨γ, rfl⟩ := h
refine DFunLike.ext'
(hp.m

Depends on / 依赖: DFunLike, DFunLike.ext, FundamentalGroup, FundamentalGroup.mapOfEq_apply, Homotopic, IsCoveringMap, IsCoveringMap.map_liftPathQuotient, Path.Homotopic.Quotient.map_cast, Quotient, h.symm, hp.isCoveringMap.liftPathQuotient, hp.isCoveringMap.monodromy_eq_of_map_eq, hp.monodromy_eq_id_iff, isCoveringMap, liftPathQuotient, mapOfEq_apply, map_cast, map_liftPathQuotient, monodromy_eq_id_iff, monodromy_eq_of_map_eq
-/
theorem ker_monodromyPerm :
    (hp.isCoveringMap.monodromyPerm x).ker =
    (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ e.2).range := by
  ext γ; constructor <;> intro h
  · refine ⟨(hp.isCoveringMap.liftPathQuotient γ e).cast rfl congr($h.symm e), ?_⟩
    rw [FundamentalGroup.mapOfEq_apply]; rw [Path.Homotopic.Quotient.map_cast]; rw [IsCoveringMap.map_liftPathQuotient]
    aesop
  · obtain ⟨γ, rfl⟩ := h
refine DFunLike.ext'
(hp.monodromy_eq_id_iff e).mpr hp.isCoveringMap.monodromy_eq_of_map_eq γ ?_
    aesop (add simp FundamentalGroup.mapOfEq_apply)

/--
theorem `monodromyPerm_injective` / 定理 `monodromyPerm_injective`

English:
theorem monodromyPerm_injective
  given: [SimplyConnectedSpace E]
  proof: by
  let e : p⁻¹' {x} := ⟨(hp.surjective x).choose, (hp.surjective x).choose_spec⟩
  rw [← MonoidHom.ker_eq_bot_iff]; rw [hp.ker_monodromyPerm e]
  set f : FundamentalGroup E (e : E) ->* FundamentalGroup X x :=
    FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ e.2
  have : Subsingleton f.range := (Set

中文:
定理 monodromyPerm_injective
  条件: [单连通空间 E]
  证明: by
  let e : p⁻¹' {x} := ⟨(hp.surjective x).choose, (hp.surjective x).choose_spec⟩
  rw [← MonoidHom.ker_eq_bot_iff]; rw [hp.ker_monodromyPerm e]
  set f : FundamentalGroup E (e : E) ->* FundamentalGroup X x :=
    FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ e.2
  have : Subsingleton f.range := (Set

Depends on / 依赖: FundamentalGroup, FundamentalGroup.mapOfEq, MonoidHom, MonoidHom.ker_eq_bot_iff, Set.subsingleton_coe, Subgroup, Subgroup.eq_bot_of_subsingleton, Subsingleton, choose_spec, continuous, eq_bot_of_subsingleton, f.range, f.subsingleton_coe_range, hp.continuous, hp.ker_monodromyPerm, hp.surjective, ker_eq_bot_iff, ker_monodromyPerm, mapOfEq, subsingleton_coe
-/
theorem monodromyPerm_injective [SimplyConnectedSpace E] :
    Injective (hp.isCoveringMap.monodromyPerm x) := by
  let e : p⁻¹' {x} := ⟨(hp.surjective x).choose, (hp.surjective x).choose_spec⟩
  rw [← MonoidHom.ker_eq_bot_iff]; rw [hp.ker_monodromyPerm e]
  set f : FundamentalGroup E (e : E) ->* FundamentalGroup X x :=
    FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ e.2
  have : Subsingleton f.range := (Set.subsingleton_coe _).mpr f.subsingleton_coe_range
  exact Subgroup.eq_bot_of_subsingleton _

open MulOpposite in
/--
Definition of `fundamentalGroupToMulOpposite` / `fundamentalGroupToMulOpposite` 的定义

English:
definition fundamentalGroupToMulOpposite
  signature: : FundamentalGroup X x ->* Gᵐᵒᵖ where
  body: op hp.fiberEquivGroup e (hp.isCoveringMap.monodromy γ e)
  map_one' := by rw [FundamentalGroup.one_def, IsCoveringMap.monodromy_refl]; simp
  map_mul' γ γ' := by
    rw [FundamentalGroup.mul_def]; rw [IsCoveringMap.monodromy_trans_apply]; rw [← op_mul]; rw [op_inj]
    apply hp.isCancelSMul.right_ca

中文:
定义 fundamentalGroupToMulOpposite
  签名: : 基本群 X x ->* Gᵐᵒᵖ where
  定义体: op hp.fiberEquivGroup e (hp.isCoveringMap.monodromy γ e)
  map_one' := by rw [FundamentalGroup.one_def, IsCoveringMap.monodromy_refl]; simp
  map_mul' γ γ' := by
    rw [FundamentalGroup.mul_def]; rw [IsCoveringMap.monodromy_trans_apply]; rw [← op_mul]; rw [op_inj]
    apply hp.isCancelSMul.right_ca

Depends on / 依赖: fiberEquivGroup, hp.fiberEquivGroup, hp.isCoveringMap.monodromy, isCoveringMap, monodromy
-/
def fundamentalGroupToMulOpposite : FundamentalGroup X x ->* Gᵐᵒᵖ where
toFun γ := op hp.fiberEquivGroup e (hp.isCoveringMap.monodromy γ e)
  map_one' := by rw [FundamentalGroup.one_def, IsCoveringMap.monodromy_refl]; simp
  map_mul' γ γ' := by
    rw [FundamentalGroup.mul_def]; rw [IsCoveringMap.monodromy_trans_apply]; rw [← op_mul]; rw [op_inj]
    apply hp.isCancelSMul.right_cancel _ _ e.1
    simp_rw [mul_smul, fiberEquivGroup_smul_self, ← hp.toPermFiber_apply_apply_coe]
    congr
    refine .trans ?_ hp.monodromy_toPermFiber
    congr
    exact Subtype.ext (fiberEquivGroup_smul_self ..).symm

variable {e} in
/--
theorem `fundamentalGroupToMulOpposite_apply_eq_Iff` / 定理 `fundamentalGroupToMulOpposite_apply_eq_Iff`

English:
theorem fundamentalGroupToMulOpposite_apply_eq_Iff
  given: {g : Gᵐᵒᵖ}
  proof: by
  rw [fundamentalGroupToMulOpposite]; rw [← MulOpposite.unop_injective.eq_iff]; rw [iff_comm]; rw [eq_comm]; rw [← hp.fiberEquivGroup_smul_self e]
  have := hp.isCancelSMul.right_cancel'
  aesop

中文:
定理 fundamentalGroupToMulOpposite_apply_eq_Iff
  条件: {g : Gᵐᵒᵖ}
  证明: by
  rw [fundamentalGroupToMulOpposite]; rw [← MulOpposite.unop_injective.eq_iff]; rw [iff_comm]; rw [eq_comm]; rw [← hp.fiberEquivGroup_smul_self e]
  have := hp.isCancelSMul.right_cancel'
  aesop

Depends on / 依赖: MulOpposite, MulOpposite.unop_injective.eq_iff, eq_comm, eq_iff, fiberEquivGroup_smul_self, fundamentalGroupToMulOpposite, hp.fiberEquivGroup_smul_self, hp.isCancelSMul.right_cancel, iff_comm, isCancelSMul, right_cancel, unop_injective
-/
theorem fundamentalGroupToMulOpposite_apply_eq_Iff {g : Gᵐᵒᵖ} :
    hp.fundamentalGroupToMulOpposite e γ = g ↔ g.unop • e.1 = hp.isCoveringMap.monodromy γ e := by
  rw [fundamentalGroupToMulOpposite]; rw [← MulOpposite.unop_injective.eq_iff]; rw [iff_comm]; rw [eq_comm]; rw [← hp.fiberEquivGroup_smul_self e]
  have := hp.isCancelSMul.right_cancel'
  aesop

variable {e} in
/--
theorem `unop_fundamentalGroupToMulOpposite_smul` / 定理 `unop_fundamentalGroupToMulOpposite_smul`

English:
theorem unop_fundamentalGroupToMulOpposite_smul
  proof: by
  simp [fundamentalGroupToMulOpposite, fiberEquivGroup_smul_self]

中文:
定理 unop_fundamentalGroupToMulOpposite_smul
  证明: by
  simp [fundamentalGroupToMulOpposite, fiberEquivGroup_smul_self]

Depends on / 依赖: fiberEquivGroup_smul_self, fundamentalGroupToMulOpposite
-/
theorem unop_fundamentalGroupToMulOpposite_smul :
    (hp.fundamentalGroupToMulOpposite e γ).unop • e.1 = hp.isCoveringMap.monodromy γ e := by
  simp [fundamentalGroupToMulOpposite, fiberEquivGroup_smul_self]

variable {e} in
/--
theorem `fundamentalGroupToMulOpposite_eq_one_iff` / 定理 `fundamentalGroupToMulOpposite_eq_one_iff`

English:
theorem fundamentalGroupToMulOpposite_eq_one_iff
  proof: Subtype.ext by rw [← hp.unop_fundamentalGroupToMulOpposite_smul, h]; apply one_smul
mpr h := MulOpposite.unop_injective hp.isCancelSMul.right_cancel _ _ e.1 by
    simp [fundamentalGroupToMulOpposite, h]

中文:
定理 fundamentalGroupToMulOpposite_eq_one_iff
  证明: Subtype.ext by rw [← hp.unop_fundamentalGroupToMulOpposite_smul, h]; apply one_smul
mpr h := MulOpposite.unop_injective hp.isCancelSMul.right_cancel _ _ e.1 by
    simp [fundamentalGroupToMulOpposite, h]

Depends on / 依赖: Subtype, Subtype.ext, hp.unop_fundamentalGroupToMulOpposite_smul, one_smul, unop_fundamentalGroupToMulOpposite_smul
-/
theorem fundamentalGroupToMulOpposite_eq_one_iff :
    hp.fundamentalGroupToMulOpposite e γ = 1 ↔ hp.isCoveringMap.monodromy γ e = e where
mp h := Subtype.ext by rw [← hp.unop_fundamentalGroupToMulOpposite_smul, h]; apply one_smul
mpr h := MulOpposite.unop_injective hp.isCancelSMul.right_cancel _ _ e.1 by
    simp [fundamentalGroupToMulOpposite, h]

/--
theorem `ker_fundamentalGroupToMulOpposite` / 定理 `ker_fundamentalGroupToMulOpposite`

English:
theorem ker_fundamentalGroupToMulOpposite
  proof: by
  ext; simp [fundamentalGroupToMulOpposite_eq_one_iff, DFunLike.ext'_iff, ← hp.monodromy_eq_id_iff]

中文:
定理 ker_fundamentalGroupToMulOpposite
  证明: by
  ext; simp [fundamentalGroupToMulOpposite_eq_one_iff, DFunLike.ext'_iff, ← hp.monodromy_eq_id_iff]

Depends on / 依赖: DFunLike, DFunLike.ext, _iff, fundamentalGroupToMulOpposite_eq_one_iff, hp.monodromy_eq_id_iff, monodromy_eq_id_iff
-/
theorem ker_fundamentalGroupToMulOpposite :
    (hp.fundamentalGroupToMulOpposite e).ker = (hp.isCoveringMap.monodromyPerm x).ker := by
  ext; simp [fundamentalGroupToMulOpposite_eq_one_iff, DFunLike.ext'_iff, ← hp.monodromy_eq_id_iff]

/--
theorem `fundamentalGroupToMulOpposite_surjective` / 定理 `fundamentalGroupToMulOpposite_surjective`

English:
theorem fundamentalGroupToMulOpposite_surjective
  given: [PathConnectedSpace E]
  proof: by
  intro g
  set e' : p⁻¹' {x} := ⟨MulOpposite.unop g • (e : E), by
    have := hp.map_smul (e := e) (MulOpposite.unop g); aesop⟩ with he'
  set Γ : Path (e : E) (e' : E) :=
    { toFun := PathConnectedSpace.somePath (e : E) (e' : E)
      continuous_toFun := by fun_prop
      source' := by simp
 

中文:
定理 fundamentalGroupToMulOpposite_surjective
  条件: [道路连通空间 E]
  证明: by
  intro g
  set e' : p⁻¹' {x} := ⟨MulOpposite.unop g • (e : E), by
    have := hp.map_smul (e := e) (MulOpposite.unop g); aesop⟩ with he'
  set Γ : Path (e : E) (e' : E) :=
    { toFun := PathConnectedSpace.somePath (e : E) (e' : E)
      continuous_toFun := by fun_prop
      source' := by simp
 

Depends on / 依赖: MulOpposite, MulOpposite.unop, PathConnectedSpace, PathConnectedSpace.somePath, continuous, continuous_toFun, e.property.symm, fromPath, fun_prop, fundamentalGroupToMulOpposite_apply_eq_Iff, hp.continuous, hp.map_smul, map_smul, property, property.symm, somePath, source, target
-/
theorem fundamentalGroupToMulOpposite_surjective [PathConnectedSpace E] :
    Surjective (hp.fundamentalGroupToMulOpposite e) := by
  intro g
  set e' : p⁻¹' {x} := ⟨MulOpposite.unop g • (e : E), by
    have := hp.map_smul (e := e) (MulOpposite.unop g); aesop⟩ with he'
  set Γ : Path (e : E) (e' : E) :=
    { toFun := PathConnectedSpace.somePath (e : E) (e' : E)
      continuous_toFun := by fun_prop
      source' := by simp
      target' := by simp }
  set γ : Path x x := (Γ.map hp.continuous).cast
    (by simpa using e.property.symm) (by simpa using e'.property.symm)
  use .fromPath ⟦γ⟧
  rw [fundamentalGroupToMulOpposite_apply_eq_Iff]
  change (e' : E) = _
  rw [← hp.isCoveringMap.monodromy_eq_of_map_eq (γ := ⟦γ⟧) (Γ := ⟦Γ⟧) rfl]

/--
lemma `fundamentalGroupToMulOpposite_injective` / 引理 `fundamentalGroupToMulOpposite_injective`

English:
lemma fundamentalGroupToMulOpposite_injective
  given: [SimplyConnectedSpace E]
  proof: by
  rw [← MonoidHom.ker_eq_bot_iff]; rw [ker_fundamentalGroupToMulOpposite]; rw [MonoidHom.ker_eq_bot_iff]
  exact hp.monodromyPerm_injective

中文:
引理 fundamentalGroupToMulOpposite_injective
  条件: [单连通空间 E]
  证明: by
  rw [← MonoidHom.ker_eq_bot_iff]; rw [ker_fundamentalGroupToMulOpposite]; rw [MonoidHom.ker_eq_bot_iff]
  exact hp.monodromyPerm_injective

Depends on / 依赖: MonoidHom, MonoidHom.ker_eq_bot_iff, hp.monodromyPerm_injective, ker_eq_bot_iff, ker_fundamentalGroupToMulOpposite, monodromyPerm_injective
-/
lemma fundamentalGroupToMulOpposite_injective [SimplyConnectedSpace E] :
    Injective (hp.fundamentalGroupToMulOpposite e) := by
  rw [← MonoidHom.ker_eq_bot_iff]; rw [ker_fundamentalGroupToMulOpposite]; rw [MonoidHom.ker_eq_bot_iff]
  exact hp.monodromyPerm_injective

/--
Definition of `fundamentalGroupEquiv` / `fundamentalGroupEquiv` 的定义

English:
definition fundamentalGroupEquiv
  signature: [SimplyConnectedSpace E]
  body: MulEquiv.ofBijective (hp.fundamentalGroupToMulOpposite e)
    ⟨hp.fundamentalGroupToMulOpposite_injective e,
     hp.fundamentalGroupToMulOpposite_surjective e⟩

中文:
定义 fundamentalGroupEquiv
  签名: [单连通空间 E]
  定义体: MulEquiv.ofBijective (hp.fundamentalGroupToMulOpposite e)
    ⟨hp.fundamentalGroupToMulOpposite_injective e,
     hp.fundamentalGroupToMulOpposite_surjective e⟩

Depends on / 依赖: MulEquiv, MulEquiv.ofBijective, fundamentalGroupToMulOpposite, fundamentalGroupToMulOpposite_injective, fundamentalGroupToMulOpposite_surjective, hp.fundamentalGroupToMulOpposite, hp.fundamentalGroupToMulOpposite_injective, hp.fundamentalGroupToMulOpposite_surjective, ofBijective
-/
def fundamentalGroupEquiv [SimplyConnectedSpace E] :
    FundamentalGroup X x ≃* Gᵐᵒᵖ :=
  MulEquiv.ofBijective (hp.fundamentalGroupToMulOpposite e)
    ⟨hp.fundamentalGroupToMulOpposite_injective e,
     hp.fundamentalGroupToMulOpposite_surjective e⟩

end IsQuotientCoveringMap

namespace IsAddQuotientCoveringMap

variable {G : Type*} [AddGroup G] [AddAction G E] (hp : IsAddQuotientCoveringMap p G) {g : G}

/--
theorem `monodromy_toPermFiber` / 定理 `monodromy_toPermFiber`

English:
theorem monodromy_toPermFiber
  given: {x y : X} {γ : Path.Homotopic.Quotient x y} {e : p ⁻¹' {x}}
  proof: hp.isCoveringMap.monodromy
    monodromy γ (hp.toMultiplicative.toPermFiber x g e) =
      hp.toMultiplicative.toPermFiber y g (monodromy γ e) :=
  hp.toMultiplicative.monodromy_toPermFiber

中文:
定理 monodromy_toPermFiber
  条件: {x y : X} {γ : 道路.同伦.商 x y} {e : p ⁻¹' {x}}
  证明: hp.isCoveringMap.monodromy
    monodromy γ (hp.toMultiplicative.toPermFiber x g e) =
      hp.toMultiplicative.toPermFiber y g (monodromy γ e) :=
  hp.toMultiplicative.monodromy_toPermFiber

Depends on / 依赖: hp.isCoveringMap.monodromy, isCoveringMap, monodromy
-/
theorem monodromy_toPermFiber {x y : X} {γ : Path.Homotopic.Quotient x y} {e : p ⁻¹' {x}} :
    letI monodromy := hp.isCoveringMap.monodromy
    monodromy γ (hp.toMultiplicative.toPermFiber x g e) =
      hp.toMultiplicative.toPermFiber y g (monodromy γ e) :=
  hp.toMultiplicative.monodromy_toPermFiber

/--
theorem `commute_monodromyPerm_toPermFiber` / 定理 `commute_monodromyPerm_toPermFiber`

English:
theorem commute_monodromyPerm_toPermFiber
  given: {x : X} {γ : FundamentalGroup X x}
  proof: hp.toMultiplicative.commute_monodromyPerm_toPermFiber

中文:
定理 commute_monodromyPerm_toPermFiber
  条件: {x : X} {γ : 基本群 X x}
  证明: hp.toMultiplicative.commute_monodromyPerm_toPermFiber

Depends on / 依赖: commute_monodromyPerm_toPermFiber, hp.toMultiplicative.commute_monodromyPerm_toPermFiber, toMultiplicative
-/
theorem commute_monodromyPerm_toPermFiber {x : X} {γ : FundamentalGroup X x} :
    Commute
      (hp.isCoveringMap.monodromyPerm x γ)
      (hp.toMultiplicative.toPermFiber x g) :=
  hp.toMultiplicative.commute_monodromyPerm_toPermFiber

/--
theorem `monodromy_ext_iff` / 定理 `monodromy_ext_iff`

English:
theorem monodromy_ext_iff
  given: {x y : X} {γ γ' : Path.Homotopic.Quotient x y} (e : p ⁻¹' {x})
  proof: hp.isCoveringMap.monodromy
    monodromy γ e = monodromy γ' e ↔ monodromy γ = monodromy γ' :=
  hp.toMultiplicative.monodromy_ext_iff e

alias ⟨monodromy_ext, _⟩ := monodromy_ext_iff

中文:
定理 monodromy_ext_iff
  条件: {x y : X} {γ γ' : 道路.同伦.商 x y} (e : p ⁻¹' {x})
  证明: hp.isCoveringMap.monodromy
    monodromy γ e = monodromy γ' e ↔ monodromy γ = monodromy γ' :=
  hp.toMultiplicative.monodromy_ext_iff e

alias ⟨monodromy_ext, _⟩ := monodromy_ext_iff

Depends on / 依赖: hp.isCoveringMap.monodromy, isCoveringMap, monodromy
-/
theorem monodromy_ext_iff {x y : X} {γ γ' : Path.Homotopic.Quotient x y} (e : p ⁻¹' {x}) :
    letI monodromy := hp.isCoveringMap.monodromy
    monodromy γ e = monodromy γ' e ↔ monodromy γ = monodromy γ' :=
  hp.toMultiplicative.monodromy_ext_iff e

alias ⟨monodromy_ext, _⟩ := monodromy_ext_iff

variable {x : X} (e : p ⁻¹' {x}) {γ : FundamentalGroup X x}

/--
theorem `monodromy_eq_id_iff` / 定理 `monodromy_eq_id_iff`

English:
theorem monodromy_eq_id_iff
  proof: hp.toMultiplicative.monodromy_eq_id_iff e

中文:
定理 monodromy_eq_id_iff
  证明: hp.toMultiplicative.monodromy_eq_id_iff e

Depends on / 依赖: hp.toMultiplicative.monodromy_eq_id_iff, monodromy_eq_id_iff, toMultiplicative
-/
theorem monodromy_eq_id_iff :
    hp.isCoveringMap.monodromy γ = id ↔ hp.isCoveringMap.monodromy γ e = e :=
  hp.toMultiplicative.monodromy_eq_id_iff e

/--
theorem `ker_monodromyPerm` / 定理 `ker_monodromyPerm`

English:
theorem ker_monodromyPerm
  proof: hp.toMultiplicative.ker_monodromyPerm e

中文:
定理 ker_monodromyPerm
  证明: hp.toMultiplicative.ker_monodromyPerm e

Depends on / 依赖: hp.toMultiplicative.ker_monodromyPerm, ker_monodromyPerm, toMultiplicative
-/
theorem ker_monodromyPerm :
    (hp.isCoveringMap.monodromyPerm x).ker =
    (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ e.2).range :=
  hp.toMultiplicative.ker_monodromyPerm e

/--
theorem `monodromyPerm_injective` / 定理 `monodromyPerm_injective`

English:
theorem monodromyPerm_injective
  given: [SimplyConnectedSpace E]
  proof: hp.toMultiplicative.monodromyPerm_injective

中文:
定理 monodromyPerm_injective
  条件: [单连通空间 E]
  证明: hp.toMultiplicative.monodromyPerm_injective

Depends on / 依赖: hp.toMultiplicative.monodromyPerm_injective, monodromyPerm_injective, toMultiplicative
-/
theorem monodromyPerm_injective [SimplyConnectedSpace E] :
    Injective (hp.isCoveringMap.monodromyPerm x) :=
  hp.toMultiplicative.monodromyPerm_injective

/--
Definition of `fundamentalGroupToMulOpposite` / `fundamentalGroupToMulOpposite` 的定义

English:
definition fundamentalGroupToMulOpposite
  signature: : FundamentalGroup X x ->* (Multiplicative G)ᵐᵒᵖ
  body: hp.toMultiplicative.fundamentalGroupToMulOpposite e

中文:
定义 fundamentalGroupToMulOpposite
  签名: : 基本群 X x ->* (Multiplicative G)ᵐᵒᵖ
  定义体: hp.toMultiplicative.fundamentalGroupToMulOpposite e

Depends on / 依赖: fundamentalGroupToMulOpposite, hp.toMultiplicative.fundamentalGroupToMulOpposite, toMultiplicative
-/
def fundamentalGroupToMulOpposite : FundamentalGroup X x ->* (Multiplicative G)ᵐᵒᵖ :=
  hp.toMultiplicative.fundamentalGroupToMulOpposite e

variable {e} in
/--
theorem `fundamentalGroupToMulOpposite_apply_eq_Iff` / 定理 `fundamentalGroupToMulOpposite_apply_eq_Iff`

English:
theorem fundamentalGroupToMulOpposite_apply_eq_Iff
  given: {g : (Multiplicative G)ᵐᵒᵖ}
  proof: hp.toMultiplicative.fundamentalGroupToMulOpposite_apply_eq_Iff

中文:
定理 fundamentalGroupToMulOpposite_apply_eq_Iff
  条件: {g : (Multiplicative G)ᵐᵒᵖ}
  证明: hp.toMultiplicative.fundamentalGroupToMulOpposite_apply_eq_Iff

Depends on / 依赖: fundamentalGroupToMulOpposite_apply_eq_Iff, hp.toMultiplicative.fundamentalGroupToMulOpposite_apply_eq_Iff, toMultiplicative
-/
theorem fundamentalGroupToMulOpposite_apply_eq_Iff {g : (Multiplicative G)ᵐᵒᵖ} :
    hp.fundamentalGroupToMulOpposite e γ = g ↔ g.unop • e.1 = hp.isCoveringMap.monodromy γ e :=
  hp.toMultiplicative.fundamentalGroupToMulOpposite_apply_eq_Iff

variable {e} in
/--
theorem `unop_fundamentalGroupToMulOpposite_smul` / 定理 `unop_fundamentalGroupToMulOpposite_smul`

English:
theorem unop_fundamentalGroupToMulOpposite_smul
  proof: hp.toMultiplicative.unop_fundamentalGroupToMulOpposite_smul

中文:
定理 unop_fundamentalGroupToMulOpposite_smul
  证明: hp.toMultiplicative.unop_fundamentalGroupToMulOpposite_smul

Depends on / 依赖: hp.toMultiplicative.unop_fundamentalGroupToMulOpposite_smul, toMultiplicative, unop_fundamentalGroupToMulOpposite_smul
-/
theorem unop_fundamentalGroupToMulOpposite_smul :
    (hp.fundamentalGroupToMulOpposite e γ).unop • e.1 = hp.isCoveringMap.monodromy γ e :=
  hp.toMultiplicative.unop_fundamentalGroupToMulOpposite_smul

variable {e} in
/--
theorem `fundamentalGroupToMulOpposite_eq_one_iff` / 定理 `fundamentalGroupToMulOpposite_eq_one_iff`

English:
theorem fundamentalGroupToMulOpposite_eq_one_iff
  proof: hp.toMultiplicative.fundamentalGroupToMulOpposite_eq_one_iff

中文:
定理 fundamentalGroupToMulOpposite_eq_one_iff
  证明: hp.toMultiplicative.fundamentalGroupToMulOpposite_eq_one_iff

Depends on / 依赖: fundamentalGroupToMulOpposite_eq_one_iff, hp.toMultiplicative.fundamentalGroupToMulOpposite_eq_one_iff, toMultiplicative
-/
theorem fundamentalGroupToMulOpposite_eq_one_iff :
    hp.fundamentalGroupToMulOpposite e γ = 1 ↔ hp.isCoveringMap.monodromy γ e = e :=
  hp.toMultiplicative.fundamentalGroupToMulOpposite_eq_one_iff

/--
theorem `ker_fundamentalGroupToMulOpposite` / 定理 `ker_fundamentalGroupToMulOpposite`

English:
theorem ker_fundamentalGroupToMulOpposite
  proof: hp.toMultiplicative.ker_fundamentalGroupToMulOpposite e

中文:
定理 ker_fundamentalGroupToMulOpposite
  证明: hp.toMultiplicative.ker_fundamentalGroupToMulOpposite e

Depends on / 依赖: hp.toMultiplicative.ker_fundamentalGroupToMulOpposite, ker_fundamentalGroupToMulOpposite, toMultiplicative
-/
theorem ker_fundamentalGroupToMulOpposite :
    (hp.fundamentalGroupToMulOpposite e).ker = (hp.isCoveringMap.monodromyPerm x).ker :=
  hp.toMultiplicative.ker_fundamentalGroupToMulOpposite e

/--
theorem `fundamentalGroupToMulOpposite_surjective` / 定理 `fundamentalGroupToMulOpposite_surjective`

English:
theorem fundamentalGroupToMulOpposite_surjective
  given: [PathConnectedSpace E]
  proof: hp.toMultiplicative.fundamentalGroupToMulOpposite_surjective e

中文:
定理 fundamentalGroupToMulOpposite_surjective
  条件: [道路连通空间 E]
  证明: hp.toMultiplicative.fundamentalGroupToMulOpposite_surjective e

Depends on / 依赖: fundamentalGroupToMulOpposite_surjective, hp.toMultiplicative.fundamentalGroupToMulOpposite_surjective, toMultiplicative
-/
theorem fundamentalGroupToMulOpposite_surjective [PathConnectedSpace E] :
    Surjective (hp.fundamentalGroupToMulOpposite e) :=
  hp.toMultiplicative.fundamentalGroupToMulOpposite_surjective e

/--
lemma `fundamentalGroupToMulOpposite_injective` / 引理 `fundamentalGroupToMulOpposite_injective`

English:
lemma fundamentalGroupToMulOpposite_injective
  given: [SimplyConnectedSpace E]
  proof: hp.toMultiplicative.fundamentalGroupToMulOpposite_injective e

中文:
引理 fundamentalGroupToMulOpposite_injective
  条件: [单连通空间 E]
  证明: hp.toMultiplicative.fundamentalGroupToMulOpposite_injective e

Depends on / 依赖: fundamentalGroupToMulOpposite_injective, hp.toMultiplicative.fundamentalGroupToMulOpposite_injective, toMultiplicative
-/
lemma fundamentalGroupToMulOpposite_injective [SimplyConnectedSpace E] :
    Injective (hp.fundamentalGroupToMulOpposite e) :=
  hp.toMultiplicative.fundamentalGroupToMulOpposite_injective e

/--
Definition of `fundamentalGroupEquiv` / `fundamentalGroupEquiv` 的定义

English:
definition fundamentalGroupEquiv
  signature: [SimplyConnectedSpace E]
  body: hp.toMultiplicative.fundamentalGroupEquiv e

中文:
定义 fundamentalGroupEquiv
  签名: [单连通空间 E]
  定义体: hp.toMultiplicative.fundamentalGroupEquiv e

Depends on / 依赖: fundamentalGroupEquiv, hp.toMultiplicative.fundamentalGroupEquiv, toMultiplicative
-/
def fundamentalGroupEquiv [SimplyConnectedSpace E] :
    FundamentalGroup X x ≃* (Multiplicative G)ᵐᵒᵖ :=
  hp.toMultiplicative.fundamentalGroupEquiv e

end IsAddQuotientCoveringMap
