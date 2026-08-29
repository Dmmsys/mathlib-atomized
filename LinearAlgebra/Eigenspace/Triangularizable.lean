/-
Copyright (c) 2020 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Spectrum
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-!
# Triangularizable linear endomorphisms

This file contains basic results relevant to the triangularizability of linear endomorphisms.

## Main definitions / results

* `Module.End.exists_eigenvalue`: in finite dimensions, over an algebraically closed field, every
  linear endomorphism has an eigenvalue.
* `Module.End.iSup_genEigenspace_eq_top`: in finite dimensions, over an algebraically
  closed field, the generalized eigenspaces of any linear endomorphism span the whole space.
* `Module.End.iSup_genEigenspace_restrict_eq_top`: in finite dimensions, if the
  generalized eigenspaces of a linear endomorphism span the whole space then the same is true of
  its restriction to any invariant submodule.

## References

* [Sheldon Axler, *Linear Algebra Done Right*][axler2024]
* https://en.wikipedia.org/wiki/Eigenvalues_and_eigenvectors

## TODO

Define triangularizable endomorphisms (e.g., as existence of a maximal chain of invariant subspaces)
and prove that in finite dimensions over a field, this is equivalent to the property that the
generalized eigenspaces span the whole space.

## Tags

eigenspace, eigenvector, eigenvalue, eigen
-/

public section

open Set Function Module Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

namespace Module.End

/--
theorem `exists_hasEigenvalue_of_genEigenspace_eq_top` / 定理 `exists_hasEigenvalue_of_genEigenspace_eq_top`

English:
theorem exists_hasEigenvalue_of_genEigenspace_eq_top
  statement: [Nontrivial M] {f : End R M} (k : Nat∞)
  proof: by
  suffices exists μ, f.HasUnifEigenvalue μ k by
    peel this with μ hμ
    exact HasUnifEigenvalue.lt zero_lt_one hμ
  simp [HasUnifEigenvalue, ← not_forall, ← iSup_eq_bot, hf]

中文:
定理 exists_hasEigenvalue_of_genEigenspace_eq_top
  结论: [Nontrivial M] {f : End R M} (k : 自然数∞)
  证明: by
  suffices exists μ, f.HasUnifEigenvalue μ k by
    peel this with μ hμ
    exact HasUnifEigenvalue.lt zero_lt_one hμ
  simp [HasUnifEigenvalue, ← not_forall, ← iSup_eq_bot, hf]

Depends on / 依赖: HasUnifEigenvalue, HasUnifEigenvalue.lt, f.HasUnifEigenvalue, iSup_eq_bot, not_forall, zero_lt_one
-/
theorem exists_hasEigenvalue_of_genEigenspace_eq_top [Nontrivial M] {f : End R M} (k : Nat∞)
    (hf : ⨆ μ, f.genEigenspace μ k = ⊤) :
    exists μ, f.HasEigenvalue μ := by
  suffices exists μ, f.HasUnifEigenvalue μ k by
    peel this with μ hμ
    exact HasUnifEigenvalue.lt zero_lt_one hμ
  simp [HasUnifEigenvalue, ← not_forall, ← iSup_eq_bot, hf]

-- This is Lemma 5.19 of [axler2024], although we are no longer following that proof.
/--
theorem `exists_eigenvalue` / 定理 `exists_eigenvalue`

English:
theorem exists_eigenvalue
  given: [IsAlgClosed K] [FiniteDimensional K V] [Nontrivial V] (f : End K V)
  proof: by
  simp_rw [hasEigenvalue_iff_mem_spectrum]
  exact spectrum.nonempty_of_isAlgClosed_of_finiteDimensional K f

中文:
定理 exists_eigenvalue
  条件: [IsAlgClosed K] [FiniteDimensional K V] [Nontrivial V] (f : End K V)
  证明: by
  simp_rw [hasEigenvalue_iff_mem_spectrum]
  exact spectrum.nonempty_of_isAlgClosed_of_finiteDimensional K f

Depends on / 依赖: hasEigenvalue_iff_mem_spectrum, nonempty_of_isAlgClosed_of_finiteDimensional, simp_rw, spectrum, spectrum.nonempty_of_isAlgClosed_of_finiteDimensional
-/
theorem exists_eigenvalue [IsAlgClosed K] [FiniteDimensional K V] [Nontrivial V] (f : End K V) :
    exists c : K, f.HasEigenvalue c := by
  simp_rw [hasEigenvalue_iff_mem_spectrum]
  exact spectrum.nonempty_of_isAlgClosed_of_finiteDimensional K f

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsAlgClosed
  signature: K] [FiniteDimensional K V] [Nontrivial V] (f
  body: ⟨⟨f.exists_eigenvalue.choose, f.exists_eigenvalue.choose_spec⟩⟩

中文:
实例 [IsAlgClosed
  签名: K] [FiniteDimensional K V] [Nontrivial V] (f
  定义体: ⟨⟨f.exists_eigenvalue.choose, f.exists_eigenvalue.choose_spec⟩⟩

Depends on / 依赖: choose_spec, exists_eigenvalue, f.exists_eigenvalue.choose, f.exists_eigenvalue.choose_spec
-/
noncomputable instance [IsAlgClosed K] [FiniteDimensional K V] [Nontrivial V] (f : End K V) :
    Inhabited f.Eigenvalues :=
  ⟨⟨f.exists_eigenvalue.choose, f.exists_eigenvalue.choose_spec⟩⟩

-- Lemma 8.22(c) of [axler2024]
/--
theorem `iSup_maxGenEigenspace_eq_top` / 定理 `iSup_maxGenEigenspace_eq_top`

English:
theorem iSup_maxGenEigenspace_eq_top
  given: [IsAlgClosed K] [FiniteDimensional K V] (f : End K V)
  proof: by
  -- We prove the claim by strong induction on the dimension of the vector space.
  suffices forall n, finrank K V = n -> ⨆ (μ : K), f.maxGenEigenspace μ = ⊤ by exact this _ rfl
  intro n h_dim
  induction n using Nat.strong_induction_on generalizing V with | h n ih =>
  rcases n with - | n
  -- 

中文:
定理 iSup_maxGenEigenspace_eq_top
  条件: [IsAlgClosed K] [FiniteDimensional K V] (f : End K V)
  证明: by
  -- We prove the claim by strong induction on the dimension of the vector space.
  suffices forall n, finrank K V = n -> ⨆ (μ : K), f.maxGenEigenspace μ = ⊤ by exact this _ rfl
  intro n h_dim
  induction n using Nat.strong_induction_on generalizing V with | h n ih =>
  rcases n with - | n
  -- 
-/
theorem iSup_maxGenEigenspace_eq_top [IsAlgClosed K] [FiniteDimensional K V] (f : End K V) :
    ⨆ (μ : K), f.maxGenEigenspace μ = ⊤ := by
  -- We prove the claim by strong induction on the dimension of the vector space.
  suffices forall n, finrank K V = n -> ⨆ (μ : K), f.maxGenEigenspace μ = ⊤ by exact this _ rfl
  intro n h_dim
  induction n using Nat.strong_induction_on generalizing V with | h n ih =>
  rcases n with - | n
  -- If the vector space is 0-dimensional, the result is trivial.
  · rw [← top_le_iff]
    simp only [Submodule.finrank_eq_zero.1 (Eq.trans (finrank_top _ _) h_dim), bot_le]
  -- Otherwise the vector space is nontrivial.
  · have : Nontrivial V := finrank_pos_iff.1 (by rw [h_dim]; apply Nat.zero_lt_succ)
    -- Hence, `f` has an eigenvalue `μ₀`.
    obtain ⟨μ₀, hμ₀⟩ : exists μ₀, f.HasEigenvalue μ₀ := exists_eigenvalue f
    -- We define `ES` to be the generalized eigenspace
    let ES := f.genEigenspace μ₀ (finrank K V)
    -- and `ER` to be the generalized eigenrange.
    let ER := f.genEigenrange μ₀ (finrank K V)
    -- `f` maps `ER` into itself.
    have h_f_ER : forall x : V, x in ER -> f x in ER := fun x hx =>
      map_genEigenrange_le (Submodule.mem_map_of_mem hx)
    -- Therefore, we can define the restriction `f'` of `f` to `ER`.
    let f' : End K ER := f.restrict h_f_ER
    -- The dimension of `ES` is positive
    have h_dim_ES_pos : 0 < finrank K ES := by
      dsimp +instances only [ES]
      rw [h_dim]
      apply pos_finrank_genEigenspace_of_hasEigenvalue hμ₀ (Nat.zero_lt_succ n)
    -- and the dimensions of `ES` and `ER` add up to `finrank K V`.
    have h_dim_add : finrank K ER + finrank K ES = finrank K V := by
      dsimp +instances only [ER, ES]
      rw [Module.End.genEigenspace_nat]; rw [Module.End.genEigenrange_nat]
      apply LinearMap.finrank_range_add_finrank_ker
    -- Therefore the dimension `ER` mus be smaller than `finrank K V`.
    have h_dim_ER : finrank K ER < n.succ := by lia
    -- This allows us to apply the induction hypothesis on `ER`:
    have ih_ER : ⨆ (μ : K), f'.maxGenEigenspace μ = ⊤ :=
      ih (finrank K ER) h_dim_ER f' rfl
    -- The induction hypothesis gives us a statement about subspaces of `ER`. We can transfer this
    -- to a statement about subspaces of `V` via `Submodule.subtype`:
    have ih_ER' : ⨆ (μ : K), (f'.maxGenEigenspace μ).map ER.subtype = ER := by
      simp only [(Submodule.map_iSup _ _).symm, ih_ER, Submodule.map_subtype_top ER]
    -- Moreover, every generalized eigenspace of `f'` is contained in the corresponding generalized
    -- eigenspace of `f`.
    have hff' :
      forall μ, (f'.maxGenEigenspace μ).map ER.subtype <= f.maxGenEigenspace μ := by
      intros
      rw [maxGenEigenspace]; rw [genEigenspace_restrict]
      apply Submodule.map_comap_le
    -- It follows that `ER` is contained in the span of all generalized eigenvectors.
    have hER : ER <= ⨆ (μ : K), f.maxGenEigenspace μ := by
      rw [← ih_ER']
      exact iSup_mono hff'
    -- `ES` is contained in this span by definition.
    have hES : ES <= ⨆ (μ : K), f.maxGenEigenspace μ :=
      ((f.genEigenspace μ₀).mono le_top).trans (le_iSup f.maxGenEigenspace μ₀)
    -- Moreover, we know that `ER` and `ES` are disjoint.
    have h_disjoint : Disjoint ER ES := generalized_eigenvec_disjoint_range_ker f μ₀
    -- Since the dimensions of `ER` and `ES` add up to the dimension of `V`, it follows that the
    -- span of all generalized eigenvectors is all of `V`.
    change ⨆ (μ : K), f.maxGenEigenspace μ = ⊤
    rw [← top_le_iff]; rw [← Submodule.eq_top_of_disjoint ER ES h_dim_add.ge h_disjoint]
    apply sup_le hER hES

end Module.End

namespace Submodule

variable {p : Submodule K V} {f : Module.End K V}

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `inf_iSup_genEigenspace` / 定理 `inf_iSup_genEigenspace`

English:
theorem inf_iSup_genEigenspace
  given: [FiniteDimensional K V] (h : forall x in p, f x in p) (k : Nat∞)
  proof: by
  refine le_antisymm (fun m hm => ?_)
    (le_inf_iff.mpr ⟨iSup_le fun μ => inf_le_left, iSup_mono fun μ => inf_le_right⟩)
  classical
  obtain ⟨hm₀ : m in p, hm₁ : m in ⨆ μ, f.genEigenspace μ k⟩ := hm
  obtain ⟨m, hm₂, rfl⟩ := (mem_iSup_iff_exists_finsupp _ _).mp hm₁
  suffices forall μ, (m μ : 

中文:
定理 inf_iSup_genEigenspace
  条件: [FiniteDimensional K V] (h : 对任意 x in p, f x in p) (k : 自然数∞)
  证明: by
  refine le_antisymm (fun m hm => ?_)
    (le_inf_iff.mpr ⟨iSup_le fun μ => inf_le_left, iSup_mono fun μ => inf_le_right⟩)
  classical
  obtain ⟨hm₀ : m in p, hm₁ : m in ⨆ μ, f.genEigenspace μ k⟩ := hm
  obtain ⟨m, hm₂, rfl⟩ := (mem_iSup_iff_exists_finsupp _ _).mp hm₁
  suffices forall μ, (m μ : 

Depends on / 依赖: Finsupp, Finsupp.notMem_support_iff.mp, classical, f.genEigenspace, genEigenspace, iSup_le, iSup_mono, inf_le_left, inf_le_right, le_antisymm, le_inf_iff, le_inf_iff.mpr, m.support, mem_iSup_iff_exists_finsupp, mem_inf, mem_inf.mp, notMem_support_iff, p.zero_mem, support, zero_mem
-/
theorem inf_iSup_genEigenspace [FiniteDimensional K V] (h : forall x in p, f x in p) (k : Nat∞) :
    p ⊓ ⨆ μ, f.genEigenspace μ k = ⨆ μ, p ⊓ f.genEigenspace μ k := by
  refine le_antisymm (fun m hm => ?_)
    (le_inf_iff.mpr ⟨iSup_le fun μ => inf_le_left, iSup_mono fun μ => inf_le_right⟩)
  classical
  obtain ⟨hm₀ : m in p, hm₁ : m in ⨆ μ, f.genEigenspace μ k⟩ := hm
  obtain ⟨m, hm₂, rfl⟩ := (mem_iSup_iff_exists_finsupp _ _).mp hm₁
  suffices forall μ, (m μ : V) in p by
    exact (mem_iSup_iff_exists_finsupp _ _).mpr ⟨m, fun μ => mem_inf.mp ⟨this μ, hm₂ μ⟩, rfl⟩
  intro μ
  by_cases hμ : μ in m.support; swap
  · simp only [Finsupp.notMem_support_iff.mp hμ, p.zero_mem]
  have hm₂_aux := hm₂
  simp_rw [Module.End.mem_genEigenspace] at hm₂_aux
  choose l hlk hl using hm₂_aux
  let l₀ : Nat := m.support.sup l
  have h_comm : forall (μ₁ μ₂ : K),
    Commute ((f - algebraMap K (End K V) μ₁) ^ l₀)
            ((f - algebraMap K (End K V) μ₂) ^ l₀) := fun μ₁ μ₂ =>
    ((Commute.sub_right rfl <| Algebra.commute_algebraMap_right _ _).sub_left
      (Algebra.commute_algebraMap_left _ _)).pow_pow _ _
  let g : End K V := (m.support.erase μ).noncommProd _ fun μ₁ _ μ₂ _ _ => h_comm μ₁ μ₂
  have hfg : Commute f g := Finset.noncommProd_commute _ _ _ _ fun μ' _ =>
    (Commute.sub_right rfl <| Algebra.commute_algebraMap_right _ _).pow_right _
  have hg₀ : g (m.sum fun _μ mμ => mμ) = g (m μ) := by
    suffices forall μ' in m.support, g (m μ') = if μ' = μ then g (m μ) else 0 by
      rw [map_finsuppSum]; rw [Finsupp.sum_congr (g2 := fun μ' _ => if μ' = μ then g (m μ) else 0) this]; rw [Finsupp.sum_ite_eq']; rw [if_pos hμ]
    rintro μ' hμ'
    split_ifs with hμμ'
    · rw [hμμ']
    have hl₀ : ((f - algebraMap K (End K V) μ') ^ l₀) (m μ') = 0 := by
      rw [← LinearMap.mem_ker]; rw [Algebra.algebraMap_eq_smul_one]; rw [← End.mem_genEigenspace_nat]
      simp_rw [← End.mem_genEigenspace_nat] at hl
      suffices (l μ' : Nat∞) <= l₀ from (f.genEigenspace μ').mono this (hl μ')
      simpa only [Nat.cast_le] using Finset.le_sup hμ'
    have : _ = g := (m.support.erase μ).noncommProd_erase_mul (Finset.mem_erase.mpr ⟨hμμ', hμ'⟩)
      (fun μ => (f - algebraMap K (End K V) μ) ^ l₀) (fun μ₁ _ μ₂ _ _ => h_comm μ₁ μ₂)
    rw [← this]; rw [Module.End.mul_apply]; rw [hl₀]; rw [_root_.map_zero]
  have hg₁ : MapsTo g p p := Finset.noncommProd_induction _ _ _ (fun g' : End K V => MapsTo g' p p)
      (fun f₁ f₂ => MapsTo.comp) (mapsTo_id _) fun μ' _ => by
    suffices MapsTo (f - algebraMap K (End K V) μ') p p by
      simp only [Module.End.coe_pow, this.iterate l₀]
    intro x hx
    rw [LinearMap.sub_apply]; rw [algebraMap_end_apply]
    exact p.sub_mem (h _ hx) (smul_mem p μ' hx)
  have hg₂ : MapsTo g ↑(f.genEigenspace μ k) ↑(f.genEigenspace μ k) :=
    f.mapsTo_genEigenspace_of_comm hfg μ k
  have hg₃ : InjOn g ↑(f.genEigenspace μ k) := by
    apply LinearMap.injOn_of_disjoint_ker subset_rfl
    have := f.independent_genEigenspace k
    have aux (μ') (_hμ' : μ' in m.support.erase μ) :
        (f.genEigenspace μ') ↑l₀ <= (f.genEigenspace μ') k := by
      apply (f.genEigenspace μ').mono
      obtain _ | k := k
      · exact le_top
· exact Nat.cast_le.2 Finset.sup_le fun i _ => Nat.cast_le.1 hlk i
    rw [LinearMap.ker_noncommProd_eq_of_supIndep_ker]; rw [← Finset.sup_eq_iSup]
    · have := Finset.supIndep_iff_disjoint_erase.mp (this.supIndep' m.support) μ hμ
      apply this.mono_right
      apply Finset.sup_mono_fun
      intro μ' hμ'
      rw [Algebra.algebraMap_eq_smul_one]; rw [← End.genEigenspace_nat]
      apply aux μ' hμ'
    · have := this.supIndep' (m.support.erase μ)
      apply this.antitone_fun
      intro μ' hμ'
      rw [Algebra.algebraMap_eq_smul_one]; rw [← End.genEigenspace_nat]
      apply aux μ' hμ'
  have hg₄ : SurjOn g
      ↑(p ⊓ f.genEigenspace μ k) ↑(p ⊓ f.genEigenspace μ k) := by
    have : MapsTo g
        ↑(p ⊓ f.genEigenspace μ k) ↑(p ⊓ f.genEigenspace μ k) :=
      hg₁.inter_inter hg₂
    rw [← LinearMap.injOn_iff_surjOn this]
    exact hg₃.mono inter_subset_right
  specialize hm₂ μ
  obtain ⟨y, ⟨hy₀ : y in p, hy₁ : y in f.genEigenspace μ k⟩, hy₂ : g y = g (m μ)⟩ :=
    hg₄ ⟨(hg₀ ▸ hg₁ hm₀), hg₂ hm₂⟩
  rwa [← hg₃ hy₁ hm₂ hy₂]

/--
theorem `eq_iSup_inf_genEigenspace` / 定理 `eq_iSup_inf_genEigenspace`

English:
theorem eq_iSup_inf_genEigenspace
  statement: [FiniteDimensional K V] (k : Nat∞)
  proof: by
  rw [← inf_iSup_genEigenspace h]; rw [h']; rw [inf_top_eq]

中文:
定理 eq_iSup_inf_genEigenspace
  结论: [FiniteDimensional K V] (k : 自然数∞)
  证明: by
  rw [← inf_iSup_genEigenspace h]; rw [h']; rw [inf_top_eq]

Depends on / 依赖: inf_iSup_genEigenspace, inf_top_eq
-/
theorem eq_iSup_inf_genEigenspace [FiniteDimensional K V] (k : Nat∞)
    (h : forall x in p, f x in p) (h' : ⨆ μ, f.genEigenspace μ k = ⊤) :
    p = ⨆ μ, p ⊓ f.genEigenspace μ k := by
  rw [← inf_iSup_genEigenspace h]; rw [h']; rw [inf_top_eq]

end Submodule

/--
theorem `Module.End.genEigenspace_restrict_eq_top` / 定理 `Module.End.genEigenspace_restrict_eq_top`

English:
theorem Module.End.genEigenspace_restrict_eq_top
  proof: by
  have := congr_arg (Submodule.comap p.subtype) (Submodule.eq_iSup_inf_genEigenspace k h h')
  have h_inj : Function.Injective p.subtype := Subtype.coe_injective
  simp_rw [Submodule.inf_genEigenspace f p h, Submodule.comap_subtype_self,
    ← Submodule.map_iSup, Submodule.comap_map_eq_of_injecti

中文:
定理 Module.End.genEigenspace_restrict_eq_top
  证明: by
  have := congr_arg (Submodule.comap p.subtype) (Submodule.eq_iSup_inf_genEigenspace k h h')
  have h_inj : Function.Injective p.subtype := Subtype.coe_injective
  simp_rw [Submodule.inf_genEigenspace f p h, Submodule.comap_subtype_self,
    ← Submodule.map_iSup, Submodule.comap_map_eq_of_injecti

Depends on / 依赖: Function, Function.Injective, Injective, Submodule, Submodule.comap, Submodule.comap_map_eq_of_injective, Submodule.comap_subtype_self, Submodule.eq_iSup_inf_genEigenspace, Submodule.inf_genEigenspace, Submodule.map_iSup, Subtype, Subtype.coe_injective, coe_injective, comap_map_eq_of_injective, comap_subtype_self, congr_arg, eq_iSup_inf_genEigenspace, h_inj, inf_genEigenspace, map_iSup
-/
theorem Module.End.genEigenspace_restrict_eq_top
    {p : Submodule K V} {f : Module.End K V} [FiniteDimensional K V] {k : Nat∞}
    (h : forall x in p, f x in p) (h' : ⨆ μ, f.genEigenspace μ k = ⊤) :
    ⨆ μ, Module.End.genEigenspace (LinearMap.restrict f h) μ k = ⊤ := by
  have := congr_arg (Submodule.comap p.subtype) (Submodule.eq_iSup_inf_genEigenspace k h h')
  have h_inj : Function.Injective p.subtype := Subtype.coe_injective
  simp_rw [Submodule.inf_genEigenspace f p h, Submodule.comap_subtype_self,
    ← Submodule.map_iSup, Submodule.comap_map_eq_of_injective h_inj] at this
  exact this.symm
