/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.RingTheory.Artinian.Module

/-!
# Modules of finite length

We define modules of finite length (`IsFiniteLength`) to be finite iterated extensions of
simple modules, and show that a module is of finite length iff it is both Noetherian and Artinian,
iff it admits a composition series.

We do not make `IsFiniteLength` a class, instead we use `[IsNoetherian R M] [IsArtinian R M]`.

## Tags

Finite length, Composition series
-/

public section

variable (R : Type*) [Ring R]

/--
Inductive type `IsFiniteLength` / 归纳类型 `IsFiniteLength`

English:
inductive IsFiniteLength
  parameters: : forall (M : Type*) [AddCommGroup M] [Module R M], Prop
  constructors (2):
    - of_subsingleton: {M} [AddCommGroup M] [Module R M] [Subsingleton M] : IsFiniteLength M
    - of_simple_quotient: {M} [AddCommGroup M] [Module R M] {N : Submodule R M} [IsSimpleModule R (M ⧸ N)] : IsFiniteLength N -> IsFiniteLength M

中文:
归纳类型 IsFiniteLength
  参数: : 对任意 (M : 类型) [AddCommGroup M] [Module R M], 命题
  构造子 (2 个):
    - of_subsingleton: {M} [AddCommGroup M] [Module R M] [Subsingleton M] : IsFiniteLength M
    - of_simple_quotient: {M} [AddCommGroup M] [Module R M] {N : Submodule R M} [IsSimpleModule R (M ⧸ N)] : IsFiniteLength N -> IsFiniteLength M
-/
inductive IsFiniteLength : forall (M : Type*) [AddCommGroup M] [Module R M], Prop
  | of_subsingleton {M} [AddCommGroup M] [Module R M] [Subsingleton M] : IsFiniteLength M
  | of_simple_quotient {M} [AddCommGroup M] [Module R M] {N : Submodule R M}
      [IsSimpleModule R (M ⧸ N)] : IsFiniteLength N -> IsFiniteLength M

attribute [nontriviality] IsFiniteLength.of_subsingleton

variable {R} {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/--
theorem `LinearEquiv.isFiniteLength` / 定理 `LinearEquiv.isFiniteLength`

English:
theorem LinearEquiv.isFiniteLength
  statement: (e : M ≃ₗ[R] N)
  proof: by
  induction h generalizing N with
  | of_subsingleton =>
    have := e.symm.toEquiv.subsingleton; exact .of_subsingleton
  | @of_simple_quotient M _ _ S _ _ ih =>
    have : IsSimpleModule R (N ⧸ Submodule.map (e : M ->ₗ[R] N) S) :=
      IsSimpleModule.congr (Submodule.Quotient.equiv S _ e rfl).

中文:
定理 LinearEquiv.isFiniteLength
  结论: (e : M ≃ₗ[R] N)
  证明: by
  induction h generalizing N with
  | of_subsingleton =>
    have := e.symm.toEquiv.subsingleton; exact .of_subsingleton
  | @of_simple_quotient M _ _ S _ _ ih =>
    have : IsSimpleModule R (N ⧸ Submodule.map (e : M ->ₗ[R] N) S) :=
      IsSimpleModule.congr (Submodule.Quotient.equiv S _ e rfl).

Depends on / 依赖: IsSimpleModule, IsSimpleModule.congr, Quotient, Submodule, Submodule.Quotient.equiv, Submodule.map, e.submoduleMap, e.symm.toEquiv.subsingleton, generalizing, of_simple_quotient, of_subsingleton, submoduleMap, subsingleton, toEquiv
-/
theorem LinearEquiv.isFiniteLength (e : M ≃ₗ[R] N)
    (h : IsFiniteLength R M) : IsFiniteLength R N := by
  induction h generalizing N with
  | of_subsingleton =>
    have := e.symm.toEquiv.subsingleton; exact .of_subsingleton
  | @of_simple_quotient M _ _ S _ _ ih =>
    have : IsSimpleModule R (N ⧸ Submodule.map (e : M ->ₗ[R] N) S) :=
      IsSimpleModule.congr (Submodule.Quotient.equiv S _ e rfl).symm
    exact .of_simple_quotient (ih <| e.submoduleMap S)

variable (R M) in
/--
theorem `exists_compositionSeries_of_isNoetherian_isArtinian` / 定理 `exists_compositionSeries_of_isNoetherian_isArtinian`

English:
theorem exists_compositionSeries_of_isNoetherian_isArtinian
  given: [IsNoetherian R M] [IsArtinian R M]
  proof: by
  obtain ⟨f, f0, n, hn⟩ := exists_covBy_seq_of_wellFoundedLT_wellFoundedGT (Submodule R M)
  exact ⟨⟨n, fun i => f i, fun i => hn.2 i i.2⟩, f0.eq_bot, hn.1.eq_top⟩

中文:
定理 exists_compositionSeries_of_isNoetherian_isArtinian
  条件: [IsNoetherian R M] [IsArtinian R M]
  证明: by
  obtain ⟨f, f0, n, hn⟩ := exists_covBy_seq_of_wellFoundedLT_wellFoundedGT (Submodule R M)
  exact ⟨⟨n, fun i => f i, fun i => hn.2 i i.2⟩, f0.eq_bot, hn.1.eq_top⟩

Depends on / 依赖: Submodule, eq_bot, eq_top, exists_covBy_seq_of_wellFoundedLT_wellFoundedGT, f0.eq_bot
-/
theorem exists_compositionSeries_of_isNoetherian_isArtinian [IsNoetherian R M] [IsArtinian R M] :
    exists s : CompositionSeries (Submodule R M), s.head = ⊥ ∧ s.last = ⊤ := by
  obtain ⟨f, f0, n, hn⟩ := exists_covBy_seq_of_wellFoundedLT_wellFoundedGT (Submodule R M)
  exact ⟨⟨n, fun i => f i, fun i => hn.2 i i.2⟩, f0.eq_bot, hn.1.eq_top⟩

/--
theorem `isFiniteLength_of_exists_compositionSeries` / 定理 `isFiniteLength_of_exists_compositionSeries`

English:
theorem isFiniteLength_of_exists_compositionSeries
  proof: Submodule.topEquiv.isFiniteLength by
    obtain ⟨s, s_head, s_last⟩ := h
    rw [← s_last]
    suffices forall i, IsFiniteLength R (s i) from this (Fin.last _)
    intro i
    induction i using Fin.induction with
    | zero => change IsFiniteLength R s.head; rw [s_head]; exact .of_subsingleton
    |

中文:
定理 isFiniteLength_of_exists_compositionSeries
  证明: Submodule.topEquiv.isFiniteLength by
    obtain ⟨s, s_head, s_last⟩ := h
    rw [← s_last]
    suffices forall i, IsFiniteLength R (s i) from this (Fin.last _)
    intro i
    induction i using Fin.induction with
    | zero => change IsFiniteLength R s.head; rw [s_head]; exact .of_subsingleton
    |

Depends on / 依赖: Fin.induction, Fin.last, IsFiniteLength, Submodule, Submodule.injective_subtype, Submodule.map_comap_subtype, Submodule.topEquiv.isFiniteLength, castSucc, cov.le, covBy_iff_quot_is_simple, equivMapOfInjective, i.castSucc, i.succ, injective_subtype, isFiniteLength, map_comap_subtype, of_subsingleton, s.head, s.step, s_head
-/
theorem isFiniteLength_of_exists_compositionSeries
    (h : exists s : CompositionSeries (Submodule R M), s.head = ⊥ ∧ s.last = ⊤) :
    IsFiniteLength R M :=
Submodule.topEquiv.isFiniteLength by
    obtain ⟨s, s_head, s_last⟩ := h
    rw [← s_last]
    suffices forall i, IsFiniteLength R (s i) from this (Fin.last _)
    intro i
    induction i using Fin.induction with
    | zero => change IsFiniteLength R s.head; rw [s_head]; exact .of_subsingleton
    | succ i ih =>
      let cov := s.step i
      have := (covBy_iff_quot_is_simple cov.le).mp cov
      have := ((s i.castSucc).comap (s i.succ).subtype).equivMapOfInjective
        _ (Submodule.injective_subtype _)
      rw [Submodule.map_comap_subtype]; rw [inf_of_le_right cov.le] at this
      exact .of_simple_quotient (this.symm.isFiniteLength ih)

/--
theorem `isFiniteLength_iff_isNoetherian_isArtinian` / 定理 `isFiniteLength_iff_isNoetherian_isArtinian`

English:
theorem isFiniteLength_iff_isNoetherian_isArtinian
  proof: open scoped IsSimpleOrder in
  ⟨fun h => h.rec (fun {M} _ _ _ => ⟨inferInstance, inferInstance⟩) fun M _ _ {N} _ _ ⟨_, _⟩ =>
    ⟨(isNoetherian_iff_submodule_quotient N).mpr ⟨‹_›, isNoetherian_iff'.mpr inferInstance⟩,
      (isArtinian_iff_submodule_quotient N).mpr ⟨‹_›, inferInstance⟩⟩,
    fun ⟨_,

中文:
定理 isFiniteLength_iff_isNoetherian_isArtinian
  证明: open scoped IsSimpleOrder in
  ⟨fun h => h.rec (fun {M} _ _ _ => ⟨inferInstance, inferInstance⟩) fun M _ _ {N} _ _ ⟨_, _⟩ =>
    ⟨(isNoetherian_iff_submodule_quotient N).mpr ⟨‹_›, isNoetherian_iff'.mpr inferInstance⟩,
      (isArtinian_iff_submodule_quotient N).mpr ⟨‹_›, inferInstance⟩⟩,
    fun ⟨_,

Depends on / 依赖: IsSimpleOrder, exists_compositionSeries_of_isNoetherian_isArtinian, h.rec, isArtinian_iff_submodule_quotient, isFiniteLength_of_exists_compositionSeries, isNoetherian_iff, isNoetherian_iff_submodule_quotient, scoped
-/
theorem isFiniteLength_iff_isNoetherian_isArtinian :
    IsFiniteLength R M ↔ IsNoetherian R M ∧ IsArtinian R M :=
  open scoped IsSimpleOrder in
  ⟨fun h => h.rec (fun {M} _ _ _ => ⟨inferInstance, inferInstance⟩) fun M _ _ {N} _ _ ⟨_, _⟩ =>
    ⟨(isNoetherian_iff_submodule_quotient N).mpr ⟨‹_›, isNoetherian_iff'.mpr inferInstance⟩,
      (isArtinian_iff_submodule_quotient N).mpr ⟨‹_›, inferInstance⟩⟩,
    fun ⟨_, _⟩ => isFiniteLength_of_exists_compositionSeries
      (exists_compositionSeries_of_isNoetherian_isArtinian R M)⟩

/--
theorem `isFiniteLength_iff_exists_compositionSeries` / 定理 `isFiniteLength_iff_exists_compositionSeries`

English:
theorem isFiniteLength_iff_exists_compositionSeries
  proof: ⟨fun h => have ⟨_, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp h
    exists_compositionSeries_of_isNoetherian_isArtinian R M,
    isFiniteLength_of_exists_compositionSeries⟩

中文:
定理 isFiniteLength_iff_exists_compositionSeries
  证明: ⟨fun h => have ⟨_, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp h
    exists_compositionSeries_of_isNoetherian_isArtinian R M,
    isFiniteLength_of_exists_compositionSeries⟩

Depends on / 依赖: exists_compositionSeries_of_isNoetherian_isArtinian, isFiniteLength_iff_isNoetherian_isArtinian, isFiniteLength_iff_isNoetherian_isArtinian.mp, isFiniteLength_of_exists_compositionSeries
-/
theorem isFiniteLength_iff_exists_compositionSeries :
    IsFiniteLength R M ↔ exists s : CompositionSeries (Submodule R M), s.head = ⊥ ∧ s.last = ⊤ :=
  ⟨fun h => have ⟨_, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp h
    exists_compositionSeries_of_isNoetherian_isArtinian R M,
    isFiniteLength_of_exists_compositionSeries⟩

open scoped IsSimpleOrder in
/--
theorem `IsSemisimpleModule.finite_tfae` / 定理 `IsSemisimpleModule.finite_tfae`

English:
theorem IsSemisimpleModule.finite_tfae
  given: [IsSemisimpleModule R M]
  proof: by
  rw [isFiniteLength_iff_isNoetherian_isArtinian]
  obtain ⟨s, hs⟩ := IsSemisimpleModule.exists_sSupIndep_sSup_simples_eq_top R M
  tfae_have 1 ↔ 2 := ⟨fun _ => inferInstance, fun _ => inferInstance⟩
  tfae_have 2 -> 5 := fun _ => ⟨s, WellFoundedGT.finite_of_sSupIndep hs.1, hs⟩
  tfae_have 3 -> 5

中文:
定理 IsSemisimpleModule.finite_tfae
  条件: [IsSemisimpleModule R M]
  证明: by
  rw [isFiniteLength_iff_isNoetherian_isArtinian]
  obtain ⟨s, hs⟩ := IsSemisimpleModule.exists_sSupIndep_sSup_simples_eq_top R M
  tfae_have 1 ↔ 2 := ⟨fun _ => inferInstance, fun _ => inferInstance⟩
  tfae_have 2 -> 5 := fun _ => ⟨s, WellFoundedGT.finite_of_sSupIndep hs.1, hs⟩
  tfae_have 3 -> 5

Depends on / 依赖: IsSemisimpleModule, IsSemisimpleModule.exists_sSupIndep_sSup_simples_eq_top, Submodule, Submodule.topEquiv.isArtinian_iff, WellFoundedGT, WellFoundedGT.finite_of_sSupIndep, WellFoundedLT, WellFoundedLT.finite_of_sSupIndep, exists_sSupIndep_sSup_simples_eq_top, finite_of_sSupIndep, isArtinian_iff, isFiniteLength_iff_isNoetherian_isArtinian, isNoetherian_top_iff, sSup_eq_t, sSup_eq_top, simple, tfae_have, topEquiv
-/
theorem IsSemisimpleModule.finite_tfae [IsSemisimpleModule R M] :
    List.TFAE [Module.Finite R M, IsNoetherian R M, IsArtinian R M, IsFiniteLength R M,
      exists s : Set (Submodule R M), s.Finite ∧ sSupIndep s ∧
        sSup s = ⊤ ∧ forall m in s, IsSimpleModule R m] := by
  rw [isFiniteLength_iff_isNoetherian_isArtinian]
  obtain ⟨s, hs⟩ := IsSemisimpleModule.exists_sSupIndep_sSup_simples_eq_top R M
  tfae_have 1 ↔ 2 := ⟨fun _ => inferInstance, fun _ => inferInstance⟩
  tfae_have 2 -> 5 := fun _ => ⟨s, WellFoundedGT.finite_of_sSupIndep hs.1, hs⟩
  tfae_have 3 -> 5 := fun _ => ⟨s, WellFoundedLT.finite_of_sSupIndep hs.1, hs⟩
  tfae_have 5 -> 4 := fun ⟨s, fin, _, sSup_eq_top, simple⟩ => by
    rw [← isNoetherian_top_iff]; rw [← Submodule.topEquiv.isArtinian_iff]; rw [← sSup_eq_top]; rw [sSup_eq_iSup]; rw [← iSup_subtype'']
    rw [SetCoe.forall'] at simple
    have := fin.to_subtype
    exact ⟨isNoetherian_iSup, isArtinian_iSup⟩
  tfae_have 4 -> 2 := And.left
  tfae_have 4 -> 3 := And.right
  tfae_finish

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsSemisimpleModule
  signature: R M] [Module.Finite R M] : IsArtinian R M
  body: (IsSemisimpleModule.finite_tfae.out 0 2).mp ‹_›

中文:
实例 [IsSemisimpleModule
  签名: R M] [Module.Finite R M] : IsArtinian R M
  定义体: (IsSemisimpleModule.finite_tfae.out 0 2).mp ‹_›

Depends on / 依赖: IsSemisimpleModule, IsSemisimpleModule.finite_tfae.out, finite_tfae
-/
instance [IsSemisimpleModule R M] [Module.Finite R M] : IsArtinian R M :=
  (IsSemisimpleModule.finite_tfae.out 0 2).mp ‹_›

variable {f : M ->ₗ[R] N}

/--
lemma `IsFiniteLength.of_injective` / 引理 `IsFiniteLength.of_injective`

English:
lemma IsFiniteLength.of_injective
  given: (H : IsFiniteLength R N) (hf : Function.Injective f)
  proof: by
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at H ⊢
  cases H
  exact ⟨isNoetherian_of_injective f hf, isArtinian_of_injective f hf⟩

中文:
引理 IsFiniteLength.of_injective
  条件: (H : IsFiniteLength R N) (hf : Function.Injective f)
  证明: by
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at H ⊢
  cases H
  exact ⟨isNoetherian_of_injective f hf, isArtinian_of_injective f hf⟩

Depends on / 依赖: isArtinian_of_injective, isFiniteLength_iff_isNoetherian_isArtinian, isNoetherian_of_injective
-/
lemma IsFiniteLength.of_injective (H : IsFiniteLength R N) (hf : Function.Injective f) :
    IsFiniteLength R M := by
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at H ⊢
  cases H
  exact ⟨isNoetherian_of_injective f hf, isArtinian_of_injective f hf⟩

/--
lemma `IsFiniteLength.of_surjective` / 引理 `IsFiniteLength.of_surjective`

English:
lemma IsFiniteLength.of_surjective
  given: (H : IsFiniteLength R M) (hf : Function.Surjective f)
  proof: by
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at H ⊢
  cases H
  exact ⟨isNoetherian_of_surjective f (LinearMap.range_eq_top.mpr hf),
    isArtinian_of_surjective _ f hf⟩

中文:
引理 IsFiniteLength.of_surjective
  条件: (H : IsFiniteLength R M) (hf : Function.Surjective f)
  证明: by
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at H ⊢
  cases H
  exact ⟨isNoetherian_of_surjective f (LinearMap.range_eq_top.mpr hf),
    isArtinian_of_surjective _ f hf⟩

Depends on / 依赖: LinearMap, LinearMap.range_eq_top.mpr, isArtinian_of_surjective, isFiniteLength_iff_isNoetherian_isArtinian, isNoetherian_of_surjective, range_eq_top
-/
lemma IsFiniteLength.of_surjective (H : IsFiniteLength R M) (hf : Function.Surjective f) :
    IsFiniteLength R N := by
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at H ⊢
  cases H
  exact ⟨isNoetherian_of_surjective f (LinearMap.range_eq_top.mpr hf),
    isArtinian_of_surjective _ f hf⟩

/- The following instances are now automatic:
example [IsSemisimpleRing R] : IsNoetherianRing R := inferInstance
example [IsSemisimpleRing R] : IsArtinianRing R := inferInstance
-/
