/-
Copyright (c) 2022 Floris van Doorn, Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Heather Macbeth
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! # The groupoid of `C^n`, fiberwise-linear maps

This file contains preliminaries for the definition of a `C^n` vector bundle: an associated
`StructureGroupoid`, the groupoid of `contMDiffFiberwiseLinear` functions.
-/

@[expose] public section

noncomputable section

open Set TopologicalSpace

open scoped Manifold Topology ContDiff

/-! ### The groupoid of `C^n`, fiberwise-linear maps -/


variable {𝕜 B F : Type*} [TopologicalSpace B]
variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

namespace FiberwiseLinear

variable {φ φ' : B -> F ≃L[𝕜] F} {U U' : Set B}

/--
Definition of `openPartialHomeomorph` / `openPartialHomeomorph` 的定义

English:
definition openPartialHomeomorph
  signature: (φ : B -> F ≃L[𝕜] F) (hU : IsOpen U)
  body: (x.1, φ x.1 x.2)
  invFun x := (x.1, (φ x.1).symm x.2)
  source := U ×ˢ univ
  target := U ×ˢ univ
  map_source' _x hx := mk_mem_prod hx.1 (mem_univ _)
  map_target' _x hx := mk_mem_prod hx.1 (mem_univ _)
  left_inv' _ _ := Prod.ext rfl (ContinuousLinearEquiv.symm_apply_apply _ _)
  right_inv' _ _ :

中文:
定义 openPartialHomeomorph
  签名: (φ : B -> F ≃L[𝕜] F) (hU : 是开集 U)
  定义体: (x.1, φ x.1 x.2)
  invFun x := (x.1, (φ x.1).symm x.2)
  source := U ×ˢ univ
  target := U ×ˢ univ
  map_source' _x hx := mk_mem_prod hx.1 (mem_univ _)
  map_target' _x hx := mk_mem_prod hx.1 (mem_univ _)
  left_inv' _ _ := Prod.ext rfl (ContinuousLinearEquiv.symm_apply_apply _ _)
  right_inv' _ _ :
-/
def openPartialHomeomorph (φ : B -> F ≃L[𝕜] F) (hU : IsOpen U)
    (hφ : ContinuousOn (fun x => φ x : B -> F ->L[𝕜] F) U)
    (h2φ : ContinuousOn (fun x => (φ x).symm : B -> F ->L[𝕜] F) U) :
    OpenPartialHomeomorph (B × F) (B × F) where
  toFun x := (x.1, φ x.1 x.2)
  invFun x := (x.1, (φ x.1).symm x.2)
  source := U ×ˢ univ
  target := U ×ˢ univ
  map_source' _x hx := mk_mem_prod hx.1 (mem_univ _)
  map_target' _x hx := mk_mem_prod hx.1 (mem_univ _)
  left_inv' _ _ := Prod.ext rfl (ContinuousLinearEquiv.symm_apply_apply _ _)
  right_inv' _ _ := Prod.ext rfl (ContinuousLinearEquiv.apply_symm_apply _ _)
  open_source := hU.prod isOpen_univ
  open_target := hU.prod isOpen_univ
  continuousOn_toFun :=
    have : ContinuousOn (fun p : B × F => ((φ p.1 : F ->L[𝕜] F), p.2)) (U ×ˢ univ) :=
      hφ.prodMap continuousOn_id
    continuousOn_fst.prodMk (isBoundedBilinearMap_apply.continuous.comp_continuousOn this)
  continuousOn_invFun :=
    have : ContinuousOn (fun p : B × F => (((φ p.1).symm : F ->L[𝕜] F), p.2)) (U ×ˢ univ) :=
      h2φ.prodMap continuousOn_id
    continuousOn_fst.prodMk (isBoundedBilinearMap_apply.continuous.comp_continuousOn this)

/--
theorem `trans_openPartialHomeomorph_apply` / 定理 `trans_openPartialHomeomorph_apply`

English:
theorem trans_openPartialHomeomorph_apply
  statement: (hU : IsOpen U)
  proof: rfl

中文:
定理 trans_openPartialHomeomorph_apply
  结论: (hU : 是开集 U)
  证明: rfl
-/
theorem trans_openPartialHomeomorph_apply (hU : IsOpen U)
    (hφ : ContinuousOn (fun x => φ x : B -> F ->L[𝕜] F) U)
    (h2φ : ContinuousOn (fun x => (φ x).symm : B -> F ->L[𝕜] F) U) (hU' : IsOpen U')
    (hφ' : ContinuousOn (fun x => φ' x : B -> F ->L[𝕜] F) U')
    (h2φ' : ContinuousOn (fun x => (φ' x).symm : B -> F ->L[𝕜] F) U') (b : B) (v : F) :
    (FiberwiseLinear.openPartialHomeomorph φ hU hφ h2φ ≫ₕ
      FiberwiseLinear.openPartialHomeomorph φ' hU' hφ' h2φ')
        ⟨b, v⟩ =
      ⟨b, φ' b (φ b v)⟩ :=
  rfl

/--
theorem `source_trans_openPartialHomeomorph` / 定理 `source_trans_openPartialHomeomorph`

English:
theorem source_trans_openPartialHomeomorph
  statement: (hU : IsOpen U)
  proof: by
  dsimp only [FiberwiseLinear.openPartialHomeomorph]; mfld_set_tac

中文:
定理 source_trans_openPartialHomeomorph
  结论: (hU : 是开集 U)
  证明: by
  dsimp only [FiberwiseLinear.openPartialHomeomorph]; mfld_set_tac

Depends on / 依赖: FiberwiseLinear, FiberwiseLinear.openPartialHomeomorph, mfld_set_tac, openPartialHomeomorph
-/
theorem source_trans_openPartialHomeomorph (hU : IsOpen U)
    (hφ : ContinuousOn (fun x => φ x : B -> F ->L[𝕜] F) U)
    (h2φ : ContinuousOn (fun x => (φ x).symm : B -> F ->L[𝕜] F) U) (hU' : IsOpen U')
    (hφ' : ContinuousOn (fun x => φ' x : B -> F ->L[𝕜] F) U')
    (h2φ' : ContinuousOn (fun x => (φ' x).symm : B -> F ->L[𝕜] F) U') :
    (FiberwiseLinear.openPartialHomeomorph φ hU hφ h2φ ≫ₕ
          FiberwiseLinear.openPartialHomeomorph φ' hU' hφ' h2φ').source =
      (U inter U') ×ˢ univ := by
  dsimp only [FiberwiseLinear.openPartialHomeomorph]; mfld_set_tac

/--
theorem `target_trans_openPartialHomeomorph` / 定理 `target_trans_openPartialHomeomorph`

English:
theorem target_trans_openPartialHomeomorph
  statement: (hU : IsOpen U)
  proof: by
  dsimp only [FiberwiseLinear.openPartialHomeomorph]; mfld_set_tac

中文:
定理 target_trans_openPartialHomeomorph
  结论: (hU : 是开集 U)
  证明: by
  dsimp only [FiberwiseLinear.openPartialHomeomorph]; mfld_set_tac

Depends on / 依赖: FiberwiseLinear, FiberwiseLinear.openPartialHomeomorph, mfld_set_tac, openPartialHomeomorph
-/
theorem target_trans_openPartialHomeomorph (hU : IsOpen U)
    (hφ : ContinuousOn (fun x => φ x : B -> F ->L[𝕜] F) U)
    (h2φ : ContinuousOn (fun x => (φ x).symm : B -> F ->L[𝕜] F) U) (hU' : IsOpen U')
    (hφ' : ContinuousOn (fun x => φ' x : B -> F ->L[𝕜] F) U')
    (h2φ' : ContinuousOn (fun x => (φ' x).symm : B -> F ->L[𝕜] F) U') :
    (FiberwiseLinear.openPartialHomeomorph φ hU hφ h2φ ≫ₕ
          FiberwiseLinear.openPartialHomeomorph φ' hU' hφ' h2φ').target =
      (U inter U') ×ˢ univ := by
  dsimp only [FiberwiseLinear.openPartialHomeomorph]; mfld_set_tac

end FiberwiseLinear

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*}
  [TopologicalSpace HB] [ChartedSpace HB B] {IB : ModelWithCorners 𝕜 EB HB}

/--
theorem `ContMDiffFiberwiseLinear.locality_aux₁` / 定理 `ContMDiffFiberwiseLinear.locality_aux₁`

English:
theorem ContMDiffFiberwiseLinear.locality_aux₁
  proof: by
  rw [SetCoe.forall'] at h
  choose s hs hsp φ u hu hφ h2φ heφ using h
  have hesu : forall p : e.source, e.source inter s p = u p ×ˢ univ := by
    intro p
    rw [← e.restr_source' (s _) (hs _)]
    exact (heφ p).1
  have hu' : forall p : e.source, (p : B × F).fst in u p := by
    intro p
    h

中文:
定理 ContMDiffFiberwiseLinear.locality_aux₁
  证明: by
  rw [SetCoe.forall'] at h
  choose s hs hsp φ u hu hφ h2φ heφ using h
  have hesu : forall p : e.source, e.source inter s p = u p ×ˢ univ := by
    intro p
    rw [← e.restr_source' (s _) (hs _)]
    exact (heφ p).1
  have hu' : forall p : e.source, (p : B × F).fst in u p := by
    intro p
    h

Depends on / 依赖: SetCoe, SetCoe.forall, and_true, e.restr_source, e.source, mem_prod, mem_univ, p.prop, q.fst, restr_source, source
-/
theorem ContMDiffFiberwiseLinear.locality_aux₁
    (n : Nat∞ω) (e : OpenPartialHomeomorph (B × F) (B × F))
    (h : forall p in e.source, exists s : Set (B × F), IsOpen s ∧ p in s ∧
      exists (φ : B -> F ≃L[𝕜] F) (u : Set B) (hu : IsOpen u)
        (hφ : ContMDiffOn IB 𝓘(𝕜, F ->L[𝕜] F) n (fun x => (φ x : F ->L[𝕜] F)) u)
        (h2φ : ContMDiffOn IB 𝓘(𝕜, F ->L[𝕜] F) n (fun x => ((φ x).symm : F ->L[𝕜] F)) u),
          (e.restr s).EqOnSource
            (FiberwiseLinear.openPartialHomeomorph φ hu hφ.continuousOn h2φ.continuousOn)) :
    exists U : Set B, e.source = U ×ˢ univ ∧ forall x in U,
        exists (φ : B -> F ≃L[𝕜] F) (u : Set B) (hu : IsOpen u) (_huU : u subseteq U) (_hux : x in u),
          exists (hφ : ContMDiffOn IB 𝓘(𝕜, F ->L[𝕜] F) n (fun x => (φ x : F ->L[𝕜] F)) u)
            (h2φ : ContMDiffOn IB 𝓘(𝕜, F ->L[𝕜] F) n (fun x => ((φ x).symm : F ->L[𝕜] F)) u),
            (e.restr (u ×ˢ univ)).EqOnSource
              (FiberwiseLinear.openPartialHomeomorph φ hu hφ.continuousOn h2φ.continuousOn) := by
  rw [SetCoe.forall'] at h
  choose s hs hsp φ u hu hφ h2φ heφ using h
  have hesu : forall p : e.source, e.source inter s p = u p ×ˢ univ := by
    intro p
    rw [← e.restr_source' (s _) (hs _)]
    exact (heφ p).1
  have hu' : forall p : e.source, (p : B × F).fst in u p := by
    intro p
    have : (p : B × F) in e.source inter s p := ⟨p.prop, hsp p⟩
    simpa only [hesu, mem_prod, mem_univ, and_true] using this
  have heu : forall p : e.source, forall q : B × F, q.fst in u p -> q in e.source := by
    intro p q hq
    have : q in u p ×ˢ (univ : Set F) := ⟨hq, trivial⟩
    rw [← hesu p] at this
    exact this.1
  have he : e.source = (Prod.fst '' e.source) ×ˢ (univ : Set F) := by
    apply subset_antisymm
    · intro p hp
      exact ⟨⟨p, hp, rfl⟩, trivial⟩
    · rintro ⟨x, v⟩ ⟨⟨p, hp, rfl : p.fst = x⟩, -⟩
      exact heu ⟨p, hp⟩ (p.fst, v) (hu' ⟨p, hp⟩)
  refine ⟨Prod.fst '' e.source, he, ?_⟩
  rintro x ⟨p, hp, rfl⟩
  refine ⟨φ ⟨p, hp⟩, u ⟨p, hp⟩, hu ⟨p, hp⟩, ?_, hu' _, hφ ⟨p, hp⟩, h2φ ⟨p, hp⟩, ?_⟩
  · intro y hy; exact ⟨(y, 0), heu ⟨p, hp⟩ ⟨_, _⟩ hy, rfl⟩
  · rw [← hesu, e.restr_source_inter]; exact heφ ⟨p, hp⟩

/--
theorem `ContMDiffFiberwiseLinear.locality_aux₂` / 定理 `ContMDiffFiberwiseLinear.locality_aux₂`

English:
theorem ContMDiffFiberwiseLinear.locality_aux₂
  proof: by
  classical
  rw [SetCoe.forall'] at h
  choose! φ u hu hUu hux hφ h2φ heφ using h
  have heuφ : forall x : U, EqOn e (fun q => (q.1, φ x q.1 q.2)) (u x ×ˢ univ) := fun x p hp => by
    refine (heφ x).2 ?_
    rw [(heφ x).1]
    exact hp
  have huφ : forall (x x' : U) (y : B), y in u x -> y in u 

中文:
定理 ContMDiffFiberwiseLinear.locality_aux₂
  证明: by
  classical
  rw [SetCoe.forall'] at h
  choose! φ u hu hUu hux hφ h2φ heφ using h
  have heuφ : forall x : U, EqOn e (fun q => (q.1, φ x q.1 q.2)) (u x ×ˢ univ) := fun x p hp => by
    refine (heφ x).2 ?_
    rw [(heφ x).1]
    exact hp
  have huφ : forall (x x' : U) (y : B), y in u x -> y in u 

Depends on / 依赖: SetCoe, SetCoe.forall, classical
-/
theorem ContMDiffFiberwiseLinear.locality_aux₂
    (n : Nat∞ω) (e : OpenPartialHomeomorph (B × F) (B × F)) (U : Set B)
    (hU : e.source = U ×ˢ univ)
    (h : forall x in U,
      exists (φ : B -> F ≃L[𝕜] F) (u : Set B) (hu : IsOpen u) (_hUu : u subseteq U) (_hux : x in u)
        (hφ : ContMDiffOn IB 𝓘(𝕜, F ->L[𝕜] F) n (fun x => (φ x : F ->L[𝕜] F)) u)
        (h2φ : ContMDiffOn IB 𝓘(𝕜, F ->L[𝕜] F) n (fun x => ((φ x).symm : F ->L[𝕜] F)) u),
          (e.restr (u ×ˢ univ)).EqOnSource
            (FiberwiseLinear.openPartialHomeomorph φ hu hφ.continuousOn h2φ.continuousOn)) :
    exists (Φ : B -> F ≃L[𝕜] F) (U : Set B) (hU₀ : IsOpen U) (hΦ :
      ContMDiffOn IB 𝓘(𝕜, F ->L[𝕜] F) n (fun x => (Φ x : F ->L[𝕜] F)) U) (h2Φ :
      ContMDiffOn IB 𝓘(𝕜, F ->L[𝕜] F) n (fun x => ((Φ x).symm : F ->L[𝕜] F)) U),
      e.EqOnSource
      (FiberwiseLinear.openPartialHomeomorph Φ hU₀ hΦ.continuousOn h2Φ.continuousOn) := by
  classical
  rw [SetCoe.forall'] at h
  choose! φ u hu hUu hux hφ h2φ heφ using h
  have heuφ : forall x : U, EqOn e (fun q => (q.1, φ x q.1 q.2)) (u x ×ˢ univ) := fun x p hp => by
    refine (heφ x).2 ?_
    rw [(heφ x).1]
    exact hp
  have huφ : forall (x x' : U) (y : B), y in u x -> y in u x' -> φ x y = φ x' y := fun p p' y hyp hyp' => by
    ext v
    have h1 : e (y, v) = (y, φ p y v) := heuφ _ ⟨(id hyp : (y, v).fst in u p), trivial⟩
    have h2 : e (y, v) = (y, φ p' y v) := heuφ _ ⟨(id hyp' : (y, v).fst in u p'), trivial⟩
    exact congr_arg Prod.snd (h1.symm.trans h2)
  have hUu' : U = ⋃ i, u i := by
    ext x
    rw [mem_iUnion]
    refine ⟨fun h => ⟨⟨x, h⟩, hux _⟩, ?_⟩
    rintro ⟨x, hx⟩
    exact hUu x hx
  have hU' : IsOpen U := by
    rw [hUu']
    apply isOpen_iUnion hu
  let Φ₀ : U -> F ≃L[𝕜] F := iUnionLift u (fun x => φ x ∘ (↑)) huφ U hUu'.le
  let Φ : B -> F ≃L[𝕜] F := fun y =>
    if hy : y in U then Φ₀ ⟨y, hy⟩ else ContinuousLinearEquiv.refl 𝕜 F
  have hΦ : forall (y) (hy : y in U), Φ y = Φ₀ ⟨y, hy⟩ := fun y hy => dif_pos hy
  have hΦφ : forall x : U, forall y in u x, Φ y = φ x y := by
    intro x y hyu
    refine (hΦ y (hUu x hyu)).trans ?_
    exact iUnionLift_mk ⟨y, hyu⟩ _
  have hΦ : ContMDiffOn IB 𝓘(𝕜, F ->L[𝕜] F) n (fun y => (Φ y : F ->L[𝕜] F)) U := by
    apply contMDiffOn_of_locally_contMDiffOn
    intro x hx
    refine ⟨u ⟨x, hx⟩, hu ⟨x, hx⟩, hux _, ?_⟩
    refine (ContMDiffOn.congr (hφ ⟨x, hx⟩) ?_).mono inter_subset_right
    intro y hy
    rw [hΦφ ⟨x]; rw [hx⟩ y hy]
  have h2Φ : ContMDiffOn IB 𝓘(𝕜, F ->L[𝕜] F) n (fun y => ((Φ y).symm : F ->L[𝕜] F)) U := by
    apply contMDiffOn_of_locally_contMDiffOn
    intro x hx
    refine ⟨u ⟨x, hx⟩, hu ⟨x, hx⟩, hux _, ?_⟩
    refine (ContMDiffOn.congr (h2φ ⟨x, hx⟩) ?_).mono inter_subset_right
    intro y hy
    rw [hΦφ ⟨x]; rw [hx⟩ y hy]
  refine ⟨Φ, U, hU', hΦ, h2Φ, hU, fun p hp => ?_⟩
  rw [hU] at hp
  rw [heuφ ⟨p.fst]; rw [hp.1⟩ ⟨hux _]; rw [hp.2⟩]
  congrm (_, ?_)
  rw [hΦφ]
  apply hux

-- Having this private lemma speeds up `simp` calls below a lot.
-- TODO: understand why and fix the underlying issue (relatedly, the `simp` calls
-- in `contMDiffFiberwiseLinear` are quite slow, even with this change)
/--
theorem `mem_aux` / 定理 `mem_aux`

English:
theorem mem_aux
  given: {e : OpenPartialHomeomorph (B × F) (B × F)} {n : Nat∞ω}
  proof: by
  simp only [mem_iUnion, mem_ofPred_eq]

中文:
定理 mem_aux
  条件: {e : OpenPartialHomeomorph (B × F) (B × F)} {n : 自然数∞ω}
  证明: by
  simp only [mem_iUnion, mem_ofPred_eq]
-/
private theorem mem_aux {e : OpenPartialHomeomorph (B × F) (B × F)} {n : Nat∞ω} :
    (e in ⋃ (φ : B -> F ≃L[𝕜] F) (U : Set B) (hU : IsOpen U)
      (hφ : ContMDiffOn IB 𝓘(𝕜, F ->L[𝕜] F) n (fun x => φ x : B -> F ->L[𝕜] F) U)
      (h2φ : ContMDiffOn IB 𝓘(𝕜, F ->L[𝕜] F) n (fun x => (φ x).symm : B -> F ->L[𝕜] F) U),
        {e | e.EqOnSource (FiberwiseLinear.openPartialHomeomorph φ hU hφ.continuousOn
          h2φ.continuousOn)}) ↔
      exists (φ : B -> F ≃L[𝕜] F) (U : Set B) (hU : IsOpen U)
        (hφ : ContMDiffOn IB 𝓘(𝕜, F ->L[𝕜] F) n (fun x => φ x : B -> F ->L[𝕜] F) U)
        (h2φ : ContMDiffOn IB 𝓘(𝕜, F ->L[𝕜] F) n (fun x => (φ x).symm : B -> F ->L[𝕜] F) U),
          e.EqOnSource
            (FiberwiseLinear.openPartialHomeomorph φ hU hφ.continuousOn h2φ.continuousOn) := by
  simp only [mem_iUnion, mem_ofPred_eq]

variable (F B IB)

/--
Definition of `contMDiffFiberwiseLinear` / `contMDiffFiberwiseLinear` 的定义

English:
definition contMDiffFiberwiseLinear
  signature: (n : Nat∞ω)
  body: ⋃ (φ : B -> F ≃L[𝕜] F) (U : Set B) (hU : IsOpen U)
      (hφ : ContMDiffOn IB 𝓘(𝕜, F ->L[𝕜] F) n (fun x => φ x : B -> F ->L[𝕜] F) U)
      (h2φ : ContMDiffOn IB 𝓘(𝕜, F ->L[𝕜] F) n (fun x => (φ x).symm : B -> F ->L[𝕜] F) U),
        {e | e.EqOnSource
          (FiberwiseLinear.openPartialHomeomorph φ

中文:
定义 contMDiffFiberwiseLinear
  签名: (n : 自然数∞ω)
  定义体: ⋃ (φ : B -> F ≃L[𝕜] F) (U : Set B) (hU : IsOpen U)
      (hφ : ContMDiffOn IB 𝓘(𝕜, F ->L[𝕜] F) n (fun x => φ x : B -> F ->L[𝕜] F) U)
      (h2φ : ContMDiffOn IB 𝓘(𝕜, F ->L[𝕜] F) n (fun x => (φ x).symm : B -> F ->L[𝕜] F) U),
        {e | e.EqOnSource
          (FiberwiseLinear.openPartialHomeomorph φ

Depends on / 依赖: ContMDiffOn, EqOnSource, FiberwiseLinear, FiberwiseLinear.openPartialHomeomorph, IsOpen, OpenPartialHom, Setoid, Setoid.trans, continuousOn, e.EqOnSource, hU.inter, mem_aux, openPartialHomeomorph
-/
def contMDiffFiberwiseLinear (n : Nat∞ω) : StructureGroupoid (B × F) where
  members :=
    ⋃ (φ : B -> F ≃L[𝕜] F) (U : Set B) (hU : IsOpen U)
      (hφ : ContMDiffOn IB 𝓘(𝕜, F ->L[𝕜] F) n (fun x => φ x : B -> F ->L[𝕜] F) U)
      (h2φ : ContMDiffOn IB 𝓘(𝕜, F ->L[𝕜] F) n (fun x => (φ x).symm : B -> F ->L[𝕜] F) U),
        {e | e.EqOnSource
          (FiberwiseLinear.openPartialHomeomorph φ hU hφ.continuousOn h2φ.continuousOn)}
  trans' := by
    simp only [mem_aux]
    rintro e e' ⟨φ, U, hU, hφ, h2φ, heφ⟩ ⟨φ', U', hU', hφ', h2φ', heφ'⟩
    refine ⟨fun b => (φ b).trans (φ' b), _, hU.inter hU', ?_, ?_,
      Setoid.trans (OpenPartialHomeomorph.EqOnSource.trans' heφ heφ') ⟨?_, ?_⟩⟩
    · change
        ContMDiffOn IB 𝓘(𝕜, F ->L[𝕜] F) n
          (fun x : B => (φ' x).toContinuousLinearMap ∘L (φ x).toContinuousLinearMap) (U inter U')
      exact (hφ'.mono inter_subset_right).clm_comp (hφ.mono inter_subset_left)
    · change
        ContMDiffOn IB 𝓘(𝕜, F ->L[𝕜] F) n
          (fun x : B => (φ x).symm.toContinuousLinearMap ∘L (φ' x).symm.toContinuousLinearMap)
          (U inter U')
      exact (h2φ.mono inter_subset_left).clm_comp (h2φ'.mono inter_subset_right)
    · apply FiberwiseLinear.source_trans_openPartialHomeomorph
    · rintro ⟨b, v⟩ -; apply FiberwiseLinear.trans_openPartialHomeomorph_apply
  symm' e := by
    simp only [mem_aux]
    rintro ⟨φ, U, hU, hφ, h2φ, heφ⟩
    refine ⟨fun b => (φ b).symm, U, hU, h2φ, ?_, OpenPartialHomeomorph.EqOnSource.symm' heφ⟩
    simp_rw [ContinuousLinearEquiv.symm_symm]
    exact hφ
  id_mem' := by
    simp_rw [mem_aux]
    refine ⟨fun _ => ContinuousLinearEquiv.refl 𝕜 F, univ, isOpen_univ, contMDiffOn_const,
      contMDiffOn_const, ⟨?_, fun b _hb => rfl⟩⟩
    simp only [FiberwiseLinear.openPartialHomeomorph, OpenPartialHomeomorph.refl_partialEquiv,
      PartialEquiv.refl_source, univ_prod_univ]
  locality' := by
    -- the hard work has been extracted to `locality_aux₁` and `locality_aux₂`
    simp only [mem_aux]
    intro e he
    obtain ⟨U, hU, h⟩ := ContMDiffFiberwiseLinear.locality_aux₁ n e he
    exact ContMDiffFiberwiseLinear.locality_aux₂ n e U hU h
  mem_of_eqOnSource' := by
    simp only [mem_aux]
    rintro e e' ⟨φ, U, hU, hφ, h2φ, heφ⟩ hee'
    exact ⟨φ, U, hU, hφ, h2φ, Setoid.trans hee' heφ⟩

@[simp]
/--
theorem `mem_contMDiffFiberwiseLinear_iff` / 定理 `mem_contMDiffFiberwiseLinear_iff`

English:
theorem mem_contMDiffFiberwiseLinear_iff
  statement: {n : Nat∞ω}
  proof: mem_aux

中文:
定理 mem_contMDiffFiberwiseLinear_iff
  结论: {n : 自然数∞ω}
  证明: mem_aux

Depends on / 依赖: mem_aux
-/
theorem mem_contMDiffFiberwiseLinear_iff {n : Nat∞ω}
    (e : OpenPartialHomeomorph (B × F) (B × F)) :
    e in contMDiffFiberwiseLinear B F IB n ↔
      exists (φ : B -> F ≃L[𝕜] F) (U : Set B) (hU : IsOpen U) (hφ :
        ContMDiffOn IB 𝓘(𝕜, F ->L[𝕜] F) n (fun x => φ x : B -> F ->L[𝕜] F) U) (h2φ :
        ContMDiffOn IB 𝓘(𝕜, F ->L[𝕜] F) n (fun x => (φ x).symm : B -> F ->L[𝕜] F) U),
        e.EqOnSource
        (FiberwiseLinear.openPartialHomeomorph φ hU hφ.continuousOn h2φ.continuousOn) :=
  mem_aux
