/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Projection

/-!
# Basis from a split exact sequence

Let `0 → K → M → P → 0` be a split exact sequence of `R`-modules, let `s : M → K` be a
retraction of `f` and `v` be a basis of `M` indexed by `κ ⊕ σ`. Then
if `s vᵢ = 0` for `i : κ` and `(s vⱼ)ⱼ` is linear independent for `j : σ`, then
the images of `vᵢ` for `i : κ` form a basis of `P`.

We treat linear independence and the span condition separately. For convenience this
is stated not for `κ ⊕ σ`, but for an arbitrary type `ι` with two maps `κ → ι` and `σ → ι`.
-/

@[expose] public section

variable {R M K P : Type*} [Ring R] [AddCommGroup M] [AddCommGroup K] [AddCommGroup P]
variable [Module R M] [Module R K] [Module R P]
variable {f : K ->ₗ[R] M} {g : M ->ₗ[R] P} {s : M ->ₗ[R] K}
variable (hs : s ∘ₗ f = LinearMap.id) (hfg : Function.Exact f g)
variable {ι κ σ : Type*} {v : ι -> M} {a : κ -> ι} {b : σ -> ι}

section
include hs hfg

/--
lemma `LinearIndependent.linearIndependent_of_exact_of_retraction` / 引理 `LinearIndependent.linearIndependent_of_exact_of_retraction`

English:
lemma LinearIndependent.linearIndependent_of_exact_of_retraction
  proof: by
  apply (LinearIndependent.comp hli a hainj).map
  rw [Submodule.disjoint_def]; rw [hfg.linearMap_ker_eq]
  rintro - hy ⟨y, rfl⟩
  have hz : s (f y) = 0 := by
    revert hy
    generalize f y = x
    intro hy
    induction hy using Submodule.span_induction with
    | mem m hm => obtain ⟨i, rfl⟩ :

中文:
引理 LinearIndependent.linearIndependent_of_exact_of_retraction
  证明: by
  apply (LinearIndependent.comp hli a hainj).map
  rw [Submodule.disjoint_def]; rw [hfg.linearMap_ker_eq]
  rintro - hy ⟨y, rfl⟩
  have hz : s (f y) = 0 := by
    revert hy
    generalize f y = x
    intro hy
    induction hy using Submodule.span_induction with
    | mem m hm => obtain ⟨i, rfl⟩ :

Depends on / 依赖: DFunLike, DFunLike.congr_fun, Function, Function.comp_apply, LinearIndependent, LinearIndependent.comp, LinearMap, LinearMap.coe_comp, LinearMap.id_coe, Submodule, Submodule.disjoint_def, Submodule.span_induction, coe_comp, comp_apply, congr_fun, disjoint_def, generalize, hfg.linearMap_ker_eq, id_coe, id_eq
-/
lemma LinearIndependent.linearIndependent_of_exact_of_retraction
    (hainj : Function.Injective a) (hsa : forall i, s (v (a i)) = 0)
    (hli : LinearIndependent R v) :
    LinearIndependent R (g ∘ v ∘ a) := by
  apply (LinearIndependent.comp hli a hainj).map
  rw [Submodule.disjoint_def]; rw [hfg.linearMap_ker_eq]
  rintro - hy ⟨y, rfl⟩
  have hz : s (f y) = 0 := by
    revert hy
    generalize f y = x
    intro hy
    induction hy using Submodule.span_induction with
    | mem m hm => obtain ⟨i, rfl⟩ := hm; apply hsa
    | zero => simp_all
    | add => simp_all
    | smul => simp_all
  replace hs := DFunLike.congr_fun hs y
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] at hs
  rw [← hs]; rw [hz]; rw [map_zero]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `top_le_span_of_aux` / 引理 `top_le_span_of_aux`

English:
lemma top_le_span_of_aux
  statement: (v : κ oplus σ -> M)
  proof: by
  rintro p -
  obtain ⟨m, rfl⟩ := hg p
  wlog h : m in LinearMap.ker s
  · let x : M := f (s m)
    rw [show g m = g (m - f (s m)) by simp [hfg.apply_apply_eq_zero]]
    apply this hs hfg v hg hslzero hli hsp
    replace hs := DFunLike.congr_fun hs (s m)
    simp only [LinearMap.coe_comp, Functio

中文:
引理 top_le_span_of_aux
  结论: (v : κ oplus σ -> M)
  证明: by
  rintro p -
  obtain ⟨m, rfl⟩ := hg p
  wlog h : m in LinearMap.ker s
  · let x : M := f (s m)
    rw [show g m = g (m - f (s m)) by simp [hfg.apply_apply_eq_zero]]
    apply this hs hfg v hg hslzero hli hsp
    replace hs := DFunLike.congr_fun hs (s m)
    simp only [LinearMap.coe_comp, Functio
-/
private lemma top_le_span_of_aux (v : κ oplus σ -> M)
    (hg : Function.Surjective g) (hslzero : forall i, s (v (.inl i)) = 0)
    (hli : LinearIndependent R (s ∘ v ∘ .inr)) (hsp : ⊤ <= Submodule.span R (Set.range v)) :
    ⊤ <= Submodule.span R (Set.range <| g ∘ v ∘ .inl) := by
  rintro p -
  obtain ⟨m, rfl⟩ := hg p
  wlog h : m in LinearMap.ker s
  · let x : M := f (s m)
    rw [show g m = g (m - f (s m)) by simp [hfg.apply_apply_eq_zero]]
    apply this hs hfg v hg hslzero hli hsp
    replace hs := DFunLike.congr_fun hs (s m)
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] at hs
    simp [hs]
  have : m in Submodule.span R (Set.range v) := hsp Submodule.mem_top
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp this
  simp only [LinearMap.mem_ker, Finsupp.sum, map_sum, map_smul,
    Finset.sum_sum_eq_sum_toLeft_add_sum_toRight, map_add, hslzero, smul_zero,
    Finset.sum_const_zero, zero_add] at h
  replace hli := (linearIndependent_iff'.mp hli) c.support.toRight (c ∘ .inr) h
  simp only [Finset.mem_toRight, Finsupp.mem_support_iff, Function.comp_apply, not_imp_self] at hli
  simp only [Finsupp.sum, Finset.sum_sum_eq_sum_toLeft_add_sum_toRight, hli, zero_smul,
    Finset.sum_const_zero, add_zero, map_sum, map_smul]
  exact Submodule.sum_mem _ (fun i hi => Submodule.smul_mem _ _ <| Submodule.subset_span ⟨i, rfl⟩)

/--
lemma `Submodule.top_le_span_of_exact_of_retraction` / 引理 `Submodule.top_le_span_of_exact_of_retraction`

English:
lemma Submodule.top_le_span_of_exact_of_retraction
  statement: (hg : Function.Surjective g)
  proof: by
  apply top_le_span_of_aux hs hfg (Sum.elim (v ∘ a) (v ∘ b)) hg hsa hlib
  simp only [codisjoint_iff, Set.sup_eq_union, Set.top_eq_univ] at hab
  rwa [Set.Sum.elim_range, Set.range_comp, Set.range_comp, ← Set.image_union, hab, Set.image_univ]

中文:
引理 子模.top_le_span_of_exact_of_retraction
  结论: (hg : 函数.满射 g)
  证明: by
  apply top_le_span_of_aux hs hfg (Sum.elim (v ∘ a) (v ∘ b)) hg hsa hlib
  simp only [codisjoint_iff, Set.sup_eq_union, Set.top_eq_univ] at hab
  rwa [Set.Sum.elim_range, Set.range_comp, Set.range_comp, ← Set.image_union, hab, Set.image_univ]

Depends on / 依赖: Set.Sum.elim_range, Set.image_union, Set.image_univ, Set.range_comp, Set.sup_eq_union, Set.top_eq_univ, Sum.elim, codisjoint_iff, elim_range, image_union, image_univ, range_comp, sup_eq_union, top_eq_univ, top_le_span_of_aux
-/
lemma Submodule.top_le_span_of_exact_of_retraction (hg : Function.Surjective g)
    (hsa : forall i, s (v (a i)) = 0) (hlib : LinearIndependent R (s ∘ v ∘ b))
    (hab : Codisjoint (Set.range a) (Set.range b))
    (hsp : ⊤ <= Submodule.span R (Set.range v)) :
    ⊤ <= Submodule.span R (Set.range <| g ∘ v ∘ a) := by
  apply top_le_span_of_aux hs hfg (Sum.elim (v ∘ a) (v ∘ b)) hg hsa hlib
  simp only [codisjoint_iff, Set.sup_eq_union, Set.top_eq_univ] at hab
  rwa [Set.Sum.elim_range, Set.range_comp, Set.range_comp, ← Set.image_union, hab, Set.image_univ]

/--
Definition of `Module.Basis.ofSplitExact` / `Module.Basis.ofSplitExact` 的定义

English:
definition Module.Basis.ofSplitExact
  signature: (hg : Function.Surjective g) (v : Basis ι R M)
  body: .mk (v.linearIndependent.linearIndependent_of_exact_of_retraction hs hfg hainj hsa)
    (Submodule.top_le_span_of_exact_of_retraction hs hfg hg hsa hlib hab (by rw [v.span_eq]))

@[simp]

中文:
定义 模.基.ofSplitExact
  签名: (hg : 函数.满射 g) (v : 基 ι R M)
  定义体: .mk (v.linearIndependent.linearIndependent_of_exact_of_retraction hs hfg hainj hsa)
    (Submodule.top_le_span_of_exact_of_retraction hs hfg hg hsa hlib hab (by rw [v.span_eq]))

@[simp]

Depends on / 依赖: Submodule, Submodule.top_le_span_of_exact_of_retraction, linearIndependent, linearIndependent_of_exact_of_retraction, span_eq, top_le_span_of_exact_of_retraction, v.linearIndependent.linearIndependent_of_exact_of_retraction, v.span_eq
-/
noncomputable def Module.Basis.ofSplitExact (hg : Function.Surjective g) (v : Basis ι R M)
    (hainj : Function.Injective a) (hsa : forall i, s (v (a i)) = 0)
    (hlib : LinearIndependent R (s ∘ v ∘ b))
    (hab : Codisjoint (Set.range a) (Set.range b)) :
    Basis κ R P :=
  .mk (v.linearIndependent.linearIndependent_of_exact_of_retraction hs hfg hainj hsa)
    (Submodule.top_le_span_of_exact_of_retraction hs hfg hg hsa hlib hab (by rw [v.span_eq]))

@[simp]
/--
lemma `Module.Basis.ofSplitExact_apply` / 引理 `Module.Basis.ofSplitExact_apply`

English:
lemma Module.Basis.ofSplitExact_apply
  statement: (hg : Function.Surjective g) (v : Basis ι R M)
  proof: by
  simp [ofSplitExact]

中文:
引理 模.基.ofSplitExact_apply
  结论: (hg : 函数.满射 g) (v : 基 ι R M)
  证明: by
  simp [ofSplitExact]

Depends on / 依赖: ofSplitExact
-/
lemma Module.Basis.ofSplitExact_apply (hg : Function.Surjective g) (v : Basis ι R M)
    (hainj : Function.Injective a) (hsa : forall i, s (v (a i)) = 0)
    (hlib : LinearIndependent R (s ∘ v ∘ b))
    (hab : Codisjoint (Set.range a) (Set.range b)) (k : κ) :
    ofSplitExact hs hfg hg v hainj hsa hlib hab k = g (v (a k)) := by
  simp [ofSplitExact]

end

section
include hfg

/--
lemma `Submodule.projectionOnto_comp_surjective_of_exact` / 引理 `Submodule.projectionOnto_comp_surjective_of_exact`

English:
lemma Submodule.projectionOnto_comp_surjective_of_exact
  proof: by
  rw [← Set.surjOn_univ]; rw [LinearMap.coe_comp]; rw [Set.surjOn_comp_iff]; rw [Set.image_univ]
  rw [← LinearMap.coe_range]; rw [← Submodule.top_coe (R := R)]; rw [surjOn_iff_le_map]; rw [← hfg.linearMap_ker_eq]
  intro x triv
  obtain ⟨a, haq, ha⟩ : g x.val in q.map g := by rwa [hmap]
  exact 

中文:
引理 子模.projectionOnto_comp_surjective_of_exact
  证明: by
  rw [← Set.surjOn_univ]; rw [LinearMap.coe_comp]; rw [Set.surjOn_comp_iff]; rw [Set.image_univ]
  rw [← LinearMap.coe_range]; rw [← Submodule.top_coe (R := R)]; rw [surjOn_iff_le_map]; rw [← hfg.linearMap_ker_eq]
  intro x triv
  obtain ⟨a, haq, ha⟩ : g x.val in q.map g := by rwa [hmap]
  exact 

Depends on / 依赖: LinearMap, LinearMap.coe_comp, LinearMap.coe_range, Set.image_univ, Set.surjOn_comp_iff, Set.surjOn_univ, Submodule, Submodule.top_coe, coe_comp, coe_range, hfg.linearMap_ker_eq, image_univ, linearMap_ker_eq, q.map, surjOn_comp_iff, surjOn_iff_le_map, surjOn_univ, top_coe, x.val
-/
lemma Submodule.projectionOnto_comp_surjective_of_exact
    {p q : Submodule R M} (hpq : IsCompl p q)
    (hmap : Submodule.map g q = ⊤) :
    Function.Surjective (Submodule.projectionOnto p q hpq ∘ₗ f) := by
  rw [← Set.surjOn_univ]; rw [LinearMap.coe_comp]; rw [Set.surjOn_comp_iff]; rw [Set.image_univ]
  rw [← LinearMap.coe_range]; rw [← Submodule.top_coe (R := R)]; rw [surjOn_iff_le_map]; rw [← hfg.linearMap_ker_eq]
  intro x triv
  obtain ⟨a, haq, ha⟩ : g x.val in q.map g := by rwa [hmap]
  exact ⟨x - a, by simp [← ha], by simpa⟩

@[deprecated (since := "2026-05-05")] alias
  Submodule.linearProjOfIsCompl_comp_surjective_of_exact :=
  Submodule.projectionOnto_comp_surjective_of_exact

/--
lemma `Submodule.projectionOnto_comp_bijective_of_exact` / 引理 `Submodule.projectionOnto_comp_bijective_of_exact`

English:
lemma Submodule.projectionOnto_comp_bijective_of_exact
  proof: by
  refine ⟨?_, Submodule.projectionOnto_comp_surjective_of_exact hfg _ hmap⟩
  rwa [LinearMap.coe_comp, Set.InjOn.injective_iff ↑(LinearMap.range f) _ subset_rfl]
  simpa [← LinearMap.disjoint_ker_iff_injOn, ← hfg.linearMap_ker_eq]

@[deprecated (since := "2026-05-05")] alias
  Submodule.linearPro

中文:
引理 子模.projectionOnto_comp_bijective_of_exact
  证明: by
  refine ⟨?_, Submodule.projectionOnto_comp_surjective_of_exact hfg _ hmap⟩
  rwa [LinearMap.coe_comp, Set.InjOn.injective_iff ↑(LinearMap.range f) _ subset_rfl]
  simpa [← LinearMap.disjoint_ker_iff_injOn, ← hfg.linearMap_ker_eq]

@[deprecated (since := "2026-05-05")] alias
  Submodule.linearPro

Depends on / 依赖: LinearMap, LinearMap.coe_comp, LinearMap.disjoint_ker_iff_injOn, LinearMap.range, Set.InjOn.injective_iff, Submodule, Submodule.projectionOnto_comp_surjective_of_exact, coe_comp, disjoint_ker_iff_injOn, hfg.linearMap_ker_eq, injective_iff, linearMap_ker_eq, projectionOnto_comp_surjective_of_exact, subset_rfl
-/
lemma Submodule.projectionOnto_comp_bijective_of_exact
    (hf : Function.Injective f) {p q : Submodule R M} (hpq : IsCompl p q)
    (hker : Disjoint (LinearMap.ker g) q) (hmap : Submodule.map g q = ⊤) :
    Function.Bijective (Submodule.projectionOnto p q hpq ∘ₗ f) := by
  refine ⟨?_, Submodule.projectionOnto_comp_surjective_of_exact hfg _ hmap⟩
  rwa [LinearMap.coe_comp, Set.InjOn.injective_iff ↑(LinearMap.range f) _ subset_rfl]
  simpa [← LinearMap.disjoint_ker_iff_injOn, ← hfg.linearMap_ker_eq]

@[deprecated (since := "2026-05-05")] alias
  Submodule.linearProjOfIsCompl_comp_bijective_of_exact :=
  Submodule.projectionOnto_comp_bijective_of_exact

/--
lemma `LinearMap.linearProjOfIsCompl_comp_bijective_of_exact` / 引理 `LinearMap.linearProjOfIsCompl_comp_bijective_of_exact`

English:
lemma LinearMap.linearProjOfIsCompl_comp_bijective_of_exact
  proof: by
  rw [LinearMap.linearProjOfIsCompl]; rw [LinearMap.comp_assoc]; rw [LinearMap.coe_comp]; rw [Function.Bijective.of_comp_iff]
  · exact (LinearEquiv.ofInjective i hi).symm.bijective
  · exact Submodule.projectionOnto_comp_bijective_of_exact hfg hf h hker hmap

中文:
引理 线性映射.linearProjOfIsCompl_comp_bijective_of_exact
  证明: by
  rw [LinearMap.linearProjOfIsCompl]; rw [LinearMap.comp_assoc]; rw [LinearMap.coe_comp]; rw [Function.Bijective.of_comp_iff]
  · exact (LinearEquiv.ofInjective i hi).symm.bijective
  · exact Submodule.projectionOnto_comp_bijective_of_exact hfg hf h hker hmap

Depends on / 依赖: Bijective, Function, Function.Bijective.of_comp_iff, LinearEquiv, LinearEquiv.ofInjective, LinearMap, LinearMap.coe_comp, LinearMap.comp_assoc, LinearMap.linearProjOfIsCompl, Submodule, Submodule.projectionOnto_comp_bijective_of_exact, bijective, coe_comp, comp_assoc, linearProjOfIsCompl, ofInjective, of_comp_iff, projectionOnto_comp_bijective_of_exact, symm.bijective
-/
lemma LinearMap.linearProjOfIsCompl_comp_bijective_of_exact
    (hf : Function.Injective f) {q : Submodule R M} {E : Type*} [AddCommGroup E] [Module R E]
    {i : E ->ₗ[R] M} (hi : Function.Injective i) (h : IsCompl (LinearMap.range i) q)
    (hker : Disjoint (LinearMap.ker g) q) (hmap : Submodule.map g q = ⊤) :
    Function.Bijective (LinearMap.linearProjOfIsCompl q i hi h ∘ₗ f) := by
  rw [LinearMap.linearProjOfIsCompl]; rw [LinearMap.comp_assoc]; rw [LinearMap.coe_comp]; rw [Function.Bijective.of_comp_iff]
  · exact (LinearEquiv.ofInjective i hi).symm.bijective
  · exact Submodule.projectionOnto_comp_bijective_of_exact hfg hf h hker hmap

end
