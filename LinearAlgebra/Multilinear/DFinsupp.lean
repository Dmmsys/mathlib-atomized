/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Sophie Morel
-/
module

public import Mathlib.Data.Fintype.Quotient
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Multilinear.Basic

/-!
# Interactions between finitely-supported functions and multilinear maps

## Main definitions

* `MultilinearMap.dfinsupp_ext`
* `MultilinearMap.dfinsuppFamily`, which satisfies
  `dfinsuppFamily f x p = f p (fun i => x i (p i))`.

  This is the finitely-supported version of `MultilinearMap.piFamily`.

  This is useful because all the intermediate results are bundled:

  - `MultilinearMap.dfinsuppFamily f x` is a `DFinsupp` supported by families of indices `p`.
  - `MultilinearMap.dfinsuppFamily f` is a `MultilinearMap` operating on finitely-supported
    functions `x`.
  - `MultilinearMap.dfinsuppFamilyₗ` is a `LinearMap`, linear in the family of multilinear maps `f`.

* `freeDFinsuppEquiv` is an equivalence of multilinear maps over free modules with finitely
  supported maps.

-/

@[expose] public section

universe uι uκ uS uR uM uN
variable {ι : Type uι} {κ : ι -> Type uκ}
variable {S : Type uS} {R : Type uR}

namespace MultilinearMap

section Semiring
variable {M : forall i, κ i -> Type uM} {N : Type uN}

variable [Finite ι] [Semiring R]
variable [forall i k, AddCommMonoid (M i k)] [AddCommMonoid N]
variable [forall i k, Module R (M i k)] [Module R N]

/-- Two multilinear maps from finitely supported functions are equal if they agree on the
generators.

This is a multilinear version of `DFinsupp.lhom_ext'`. -/
@[ext]
/--
theorem `dfinsupp_ext` / 定理 `dfinsupp_ext`

English:
theorem dfinsupp_ext
  statement: [forall i, DecidableEq (κ i)]
  proof: by
  ext x
  change f (fun i => x i) = g (fun i => x i)
  classical
  cases nonempty_fintype ι
  rw [funext (fun i => Eq.symm (DFinsupp.sum_single (f := x i)))]
  simp_rw [DFinsupp.sum, MultilinearMap.map_sum_finset]
  congr! 1 with p
  simp_rw [MultilinearMap.ext_iff] at h
  exact h _ _

中文:
定理 dfinsupp_ext
  结论: [对任意 i, DecidableEq (κ i)]
  证明: by
  ext x
  change f (fun i => x i) = g (fun i => x i)
  classical
  cases nonempty_fintype ι
  rw [funext (fun i => Eq.symm (DFinsupp.sum_single (f := x i)))]
  simp_rw [DFinsupp.sum, MultilinearMap.map_sum_finset]
  congr! 1 with p
  simp_rw [MultilinearMap.ext_iff] at h
  exact h _ _

Depends on / 依赖: DFinsupp, DFinsupp.sum, DFinsupp.sum_single, Eq.symm, MultilinearMap, MultilinearMap.ext_iff, MultilinearMap.map_sum_finset, classical, ext_iff, map_sum_finset, nonempty_fintype, simp_rw, sum_single
-/
theorem dfinsupp_ext [forall i, DecidableEq (κ i)]
    ⦃f g : MultilinearMap R (fun i => Π₀ j : κ i, M i j) N⦄
    (h : forall p : Π i, κ i,
      f.compLinearMap (fun i => DFinsupp.lsingle (p i)) =
      g.compLinearMap (fun i => DFinsupp.lsingle (p i))) : f = g := by
  ext x
  change f (fun i => x i) = g (fun i => x i)
  classical
  cases nonempty_fintype ι
  rw [funext (fun i => Eq.symm (DFinsupp.sum_single (f := x i)))]
  simp_rw [DFinsupp.sum, MultilinearMap.map_sum_finset]
  congr! 1 with p
  simp_rw [MultilinearMap.ext_iff] at h
  exact h _ _

end Semiring

section dfinsuppFamily
variable {M : forall i, κ i -> Type uM} {N : (Π i, κ i) -> Type uN}

section Semiring

variable [DecidableEq ι] [Fintype ι] [Semiring R]
variable [forall i k, AddCommMonoid (M i k)] [forall p, AddCommMonoid (N p)]
variable [forall i k, Module R (M i k)] [forall p, Module R (N p)]

set_option backward.isDefEq.respectTransparency false in
/--
Given a family of indices `κ` and a multilinear map `f p` for each way `p` to select one index from
each family, `dfinsuppFamily f` maps a family of finitely-supported functions (one for each domain
`κ i`) into a finitely-supported function from each selection of indices (with domain `Π i, κ i`).

Strictly this doesn't need multilinearity, only the fact that `f p m = 0` whenever `m i = 0` for
some `i`.

This is the `DFinsupp` version of `MultilinearMap.piFamily`.
-/
@[simps]
/--
Definition of `dfinsuppFamily` / `dfinsuppFamily` 的定义

English:
definition dfinsuppFamily
  body: { toFun := fun p => f p (fun i => x i (p i))
    support' := (Trunc.finChoice fun i => (x i).support').map fun s => ⟨
.map fun f i => f i (Finset.mem_univ _), Finset.univ.val.pi (fun i => (s i).val)
      fun p => by
        simp only [Multiset.mem_map, Multiset.mem_pi, Finset.mem_val, Finset.mem_un

中文:
定义 dfinsuppFamily
  定义体: { toFun := fun p => f p (fun i => x i (p i))
    support' := (Trunc.finChoice fun i => (x i).support').map fun s => ⟨
.map fun f i => f i (Finset.mem_univ _), Finset.univ.val.pi (fun i => (s i).val)
      fun p => by
        simp only [Multiset.mem_map, Multiset.mem_pi, Finset.mem_val, Finset.mem_un

Depends on / 依赖: Finset, Finset.mem_univ, Finset.mem_val, Finset.univ.val.pi, Multiset, Multiset.mem_map, Multiset.mem_pi, Trunc.finChoice, finChoice, forall_true_left, map_coord_zero, map_update_ad, mem_map, mem_pi, mem_univ, mem_val, or_iff_not_imp_right, resolve_right, simp_rw, support
-/
def dfinsuppFamily
    (f : Π (p : Π i, κ i), MultilinearMap R (fun i => M i (p i)) (N p)) :
    MultilinearMap R (fun i => Π₀ j : κ i, M i j) (Π₀ t : Π i, κ i, N t) where
  toFun x :=
  { toFun := fun p => f p (fun i => x i (p i))
    support' := (Trunc.finChoice fun i => (x i).support').map fun s => ⟨
.map fun f i => f i (Finset.mem_univ _), Finset.univ.val.pi (fun i => (s i).val)
      fun p => by
        simp only [Multiset.mem_map, Multiset.mem_pi, Finset.mem_val, Finset.mem_univ,
          forall_true_left]
        simp_rw [or_iff_not_imp_right]
        intro h
        push Not at h
.resolve_right ?_, rfl⟩ refine ⟨fun i _ => p i, fun i => (s i).prop _
        exact mt ((f p).map_coord_zero (m := fun i => x i _) i) h⟩}
  map_update_add' {dec} m i x y := DFinsupp.ext fun p => by
    dsimp
    simp_rw [Function.apply_update (fun i m => m (p i)) m, DFinsupp.add_apply, (f p).map_update_add]
  map_update_smul' {dec} m i c x := DFinsupp.ext fun p => by
    dsimp
    simp_rw [Function.apply_update (fun i m => m (p i)) m, DFinsupp.smul_apply,
      (f p).map_update_smul]

/--
theorem `support_dfinsuppFamily_subset` / 定理 `support_dfinsuppFamily_subset`

English:
theorem support_dfinsuppFamily_subset
  proof: by
  intro p hp
  simp only [DFinsupp.mem_support_toFun, dfinsuppFamily_apply_toFun, ne_eq,
    Fintype.mem_piFinset] at hp ⊢
  intro i
  exact mt ((f p).map_coord_zero (m := fun i => x i _) i) hp

中文:
定理 support_dfinsuppFamily_subset
  证明: by
  intro p hp
  simp only [DFinsupp.mem_support_toFun, dfinsuppFamily_apply_toFun, ne_eq,
    Fintype.mem_piFinset] at hp ⊢
  intro i
  exact mt ((f p).map_coord_zero (m := fun i => x i _) i) hp

Depends on / 依赖: DFinsupp, DFinsupp.mem_support_toFun, Fintype, Fintype.mem_piFinset, dfinsuppFamily_apply_toFun, map_coord_zero, mem_piFinset, mem_support_toFun, ne_eq
-/
theorem support_dfinsuppFamily_subset
    [forall i, DecidableEq (κ i)]
    [forall i j, (x : M i j) -> Decidable (x != 0)] [forall i, (x : N i) -> Decidable (x != 0)]
    (f : Π (p : Π i, κ i), MultilinearMap R (fun i => M i (p i)) (N p))
    (x : forall i, Π₀ j : κ i, M i j) :
    (dfinsuppFamily f x).support subseteq Fintype.piFinset fun i => (x i).support := by
  intro p hp
  simp only [DFinsupp.mem_support_toFun, dfinsuppFamily_apply_toFun, ne_eq,
    Fintype.mem_piFinset] at hp ⊢
  intro i
  exact mt ((f p).map_coord_zero (m := fun i => x i _) i) hp

/-- When applied to a family of finitely-supported functions each supported on a single element,
`dfinsuppFamily` is itself supported on a single element, with value equal to the map `f` applied
at that point. -/
@[simp]
/--
theorem `dfinsuppFamily_single` / 定理 `dfinsuppFamily_single`

English:
theorem dfinsuppFamily_single
  statement: [forall i, DecidableEq (κ i)]
  proof: by
  ext q
  obtain rfl | hpq := eq_or_ne q p
  · simp
  · rw [DFinsupp.single_eq_of_ne hpq]
    rw [Function.ne_iff] at hpq
    obtain ⟨i, hpqi⟩ := hpq
    apply (f q).map_coord_zero i
    simp_rw [DFinsupp.single_eq_of_ne hpqi]

中文:
定理 dfinsuppFamily_single
  结论: [对任意 i, DecidableEq (κ i)]
  证明: by
  ext q
  obtain rfl | hpq := eq_or_ne q p
  · simp
  · rw [DFinsupp.single_eq_of_ne hpq]
    rw [Function.ne_iff] at hpq
    obtain ⟨i, hpqi⟩ := hpq
    apply (f q).map_coord_zero i
    simp_rw [DFinsupp.single_eq_of_ne hpqi]

Depends on / 依赖: DFinsupp, DFinsupp.single_eq_of_ne, Function, Function.ne_iff, eq_or_ne, map_coord_zero, ne_iff, simp_rw, single_eq_of_ne
-/
theorem dfinsuppFamily_single [forall i, DecidableEq (κ i)]
    (f : Π (p : Π i, κ i), MultilinearMap R (fun i => M i (p i)) (N p))
    (p : forall i, κ i) (m : forall i, M i (p i)) :
    dfinsuppFamily f (fun i => .single (p i) (m i)) = DFinsupp.single p (f p m) := by
  ext q
  obtain rfl | hpq := eq_or_ne q p
  · simp
  · rw [DFinsupp.single_eq_of_ne hpq]
    rw [Function.ne_iff] at hpq
    obtain ⟨i, hpqi⟩ := hpq
    apply (f q).map_coord_zero i
    simp_rw [DFinsupp.single_eq_of_ne hpqi]

/-- When only one member of the family of multilinear maps is nonzero, the result consists only of
the component from that member. -/
@[simp]
/--
theorem `dfinsuppFamily_single_left_apply` / 定理 `dfinsuppFamily_single_left_apply`

English:
theorem dfinsuppFamily_single_left_apply
  statement: [forall i, DecidableEq (κ i)]
  proof: by
  ext p'
  obtain rfl | hp := eq_or_ne p p'
  · simp
  · simp [hp]

中文:
定理 dfinsuppFamily_single_left_apply
  结论: [对任意 i, DecidableEq (κ i)]
  证明: by
  ext p'
  obtain rfl | hp := eq_or_ne p p'
  · simp
  · simp [hp]

Depends on / 依赖: eq_or_ne
-/
theorem dfinsuppFamily_single_left_apply [forall i, DecidableEq (κ i)]
    (p : Π i, κ i) (f : MultilinearMap R (fun i => M i (p i)) (N p)) (x : Π i, Π₀ j, M i j) :
    dfinsuppFamily (Pi.single p f) x = DFinsupp.single p (f fun i => x _ (p i)) := by
  ext p'
  obtain rfl | hp := eq_or_ne p p'
  · simp
  · simp [hp]

/--
theorem `dfinsuppFamily_single_left` / 定理 `dfinsuppFamily_single_left`

English:
theorem dfinsuppFamily_single_left
  statement: [forall i, DecidableEq (κ i)]
  proof: ext dfinsuppFamily_single_left_apply _ _

@[simp]

中文:
定理 dfinsuppFamily_single_left
  结论: [对任意 i, DecidableEq (κ i)]
  证明: ext dfinsuppFamily_single_left_apply _ _

@[simp]

Depends on / 依赖: dfinsuppFamily_single_left_apply
-/
theorem dfinsuppFamily_single_left [forall i, DecidableEq (κ i)]
    (p : Π i, κ i) (f : MultilinearMap R (fun i => M i (p i)) (N p)) :
    dfinsuppFamily (Pi.single p f) =
      (DFinsupp.lsingle p).compMultilinearMap (f.compLinearMap fun i => DFinsupp.lapply (p i)) :=
ext dfinsuppFamily_single_left_apply _ _

@[simp]
/--
theorem `dfinsuppFamily_compLinearMap_lsingle` / 定理 `dfinsuppFamily_compLinearMap_lsingle`

English:
theorem dfinsuppFamily_compLinearMap_lsingle
  statement: [forall i, DecidableEq (κ i)]
  proof: MultilinearMap.ext dfinsuppFamily_single f p

@[simp]

中文:
定理 dfinsuppFamily_compLinearMap_lsingle
  结论: [对任意 i, DecidableEq (κ i)]
  证明: MultilinearMap.ext dfinsuppFamily_single f p

@[simp]

Depends on / 依赖: MultilinearMap, MultilinearMap.ext, dfinsuppFamily_single
-/
theorem dfinsuppFamily_compLinearMap_lsingle [forall i, DecidableEq (κ i)]
    (f : Π (p : Π i, κ i), MultilinearMap R (fun i => M i (p i)) (N p)) (p : forall i, κ i) :
    (dfinsuppFamily f).compLinearMap (fun i => DFinsupp.lsingle (p i))
      = (DFinsupp.lsingle p).compMultilinearMap (f p) :=
MultilinearMap.ext dfinsuppFamily_single f p

@[simp]
/--
theorem `dfinsuppFamily_zero` / 定理 `dfinsuppFamily_zero`

English:
theorem dfinsuppFamily_zero
  proof: by
  ext; simp

@[simp]

中文:
定理 dfinsuppFamily_zero
  证明: by
  ext; simp

@[simp]
-/
theorem dfinsuppFamily_zero :
    dfinsuppFamily (0 : Π (p : Π i, κ i), MultilinearMap R (fun i => M i (p i)) (N p)) = 0 := by
  ext; simp

@[simp]
/--
theorem `dfinsuppFamily_add` / 定理 `dfinsuppFamily_add`

English:
theorem dfinsuppFamily_add
  given: (f g : Π (p : Π i, κ i), MultilinearMap R (fun i => M i (p i)) (N p))
  proof: by
  ext; simp

@[simp]

中文:
定理 dfinsuppFamily_add
  条件: (f g : Π (p : Π i, κ i), 多重线性映射 R (fun i => M i (p i)) (N p))
  证明: by
  ext; simp

@[simp]
-/
theorem dfinsuppFamily_add (f g : Π (p : Π i, κ i), MultilinearMap R (fun i => M i (p i)) (N p)) :
    dfinsuppFamily (f + g) = dfinsuppFamily f + dfinsuppFamily g := by
  ext; simp

@[simp]
/--
theorem `dfinsuppFamily_smul` / 定理 `dfinsuppFamily_smul`

English:
theorem dfinsuppFamily_smul
  proof: by
  ext; simp

中文:
定理 dfinsuppFamily_smul
  证明: by
  ext; simp
-/
theorem dfinsuppFamily_smul
    [Monoid S] [forall p, DistribMulAction S (N p)] [forall p, SMulCommClass R S (N p)]
    (s : S) (f : Π (p : Π i, κ i), MultilinearMap R (fun i => M i (p i)) (N p)) :
    dfinsuppFamily (s • f) = s • dfinsuppFamily f := by
  ext; simp

end Semiring

section CommSemiring

variable [DecidableEq ι] [Fintype ι] [CommSemiring R]
variable [forall i k, AddCommMonoid (M i k)] [forall p, AddCommMonoid (N p)]
variable [forall i k, Module R (M i k)] [forall p, Module R (N p)]

/-- `MultilinearMap.dfinsuppFamily` as a linear map. -/
@[simps]
/--
Definition of `dfinsuppFamilyₗ` / `dfinsuppFamilyₗ` 的定义

English:
definition dfinsuppFamilyₗ
  signature: :
  body: dfinsuppFamily
  map_add' := dfinsuppFamily_add
  map_smul' := dfinsuppFamily_smul

中文:
定义 dfinsuppFamilyₗ
  签名: :
  定义体: dfinsuppFamily
  map_add' := dfinsuppFamily_add
  map_smul' := dfinsuppFamily_smul

Depends on / 依赖: dfinsuppFamily
-/
def dfinsuppFamilyₗ :
    (Π (p : Π i, κ i), MultilinearMap R (fun i => M i (p i)) (N p))
      ->ₗ[R] MultilinearMap R (fun i => Π₀ j : κ i, M i j) (Π₀ t : Π i, κ i, N t) where
  toFun := dfinsuppFamily
  map_add' := dfinsuppFamily_add
  map_smul' := dfinsuppFamily_smul

variable {N : Type*} [AddCommMonoid N] [Module R N] [(i : ι) -> DecidableEq (κ i)]

variable (R κ) in
/--
Definition of `fromDFinsuppEquiv` / `fromDFinsuppEquiv` 的定义

English:
definition fromDFinsuppEquiv
  signature: :
  body: LinearEquiv.ofLinearMap
    ((DFinsupp.lsum Nat fun _ => .id).compMultilinearMapₗ R ∘ₗ MultilinearMap.dfinsuppFamilyₗ)
    (LinearMap.pi fun p => MultilinearMap.compLinearMapₗ fun i => DFinsupp.lsingle (p i))
    (by ext f x; simp)
    (by ext f p a; simp)

@[simp]

中文:
定义 fromDFinsuppEquiv
  签名: :
  定义体: LinearEquiv.ofLinearMap
    ((DFinsupp.lsum Nat fun _ => .id).compMultilinearMapₗ R ∘ₗ MultilinearMap.dfinsuppFamilyₗ)
    (LinearMap.pi fun p => MultilinearMap.compLinearMapₗ fun i => DFinsupp.lsingle (p i))
    (by ext f x; simp)
    (by ext f p a; simp)

@[simp]

Depends on / 依赖: DFinsupp, DFinsupp.lsingle, DFinsupp.lsum, LinearEquiv, LinearEquiv.ofLinearMap, LinearMap, LinearMap.pi, MultilinearMap, MultilinearMap.compLinearMap, MultilinearMap.dfinsuppFamily, lsingle, ofLinearMap
-/
def fromDFinsuppEquiv :
    ((p : Π i, κ i) -> MultilinearMap R (fun i => M i (p i)) N) ≃ₗ[R]
      MultilinearMap R (fun i => Π₀ j : κ i, M i j) N :=
  LinearEquiv.ofLinearMap
    ((DFinsupp.lsum Nat fun _ => .id).compMultilinearMapₗ R ∘ₗ MultilinearMap.dfinsuppFamilyₗ)
    (LinearMap.pi fun p => MultilinearMap.compLinearMapₗ fun i => DFinsupp.lsingle (p i))
    (by ext f x; simp)
    (by ext f p a; simp)

@[simp]
/--
theorem `fromDFinsuppEquiv_single` / 定理 `fromDFinsuppEquiv_single`

English:
theorem fromDFinsuppEquiv_single
  proof: by
  simp [fromDFinsuppEquiv]

中文:
定理 fromDFinsuppEquiv_single
  证明: by
  simp [fromDFinsuppEquiv]

Depends on / 依赖: fromDFinsuppEquiv
-/
theorem fromDFinsuppEquiv_single
    (f : Π (p : Π i, κ i), MultilinearMap R (fun i => M i (p i)) N)
    (p : Π i, κ i) (x : Π i, M i (p i)) :
    fromDFinsuppEquiv κ R f (fun i => DFinsupp.single (p i) (x i)) = f p x := by
  simp [fromDFinsuppEquiv]

/--
theorem `fromDFinsuppEquiv_apply` / 定理 `fromDFinsuppEquiv_apply`

English:
theorem fromDFinsuppEquiv_apply
  proof: by
  classical
  refine (DFinsupp.sumAddHom_apply _ _).trans ?_
  refine Finset.sum_subset (MultilinearMap.support_dfinsuppFamily_subset _ _) ?_
  simp

@[simp]

中文:
定理 fromDFinsuppEquiv_apply
  证明: by
  classical
  refine (DFinsupp.sumAddHom_apply _ _).trans ?_
  refine Finset.sum_subset (MultilinearMap.support_dfinsuppFamily_subset _ _) ?_
  simp

@[simp]

Depends on / 依赖: DFinsupp, DFinsupp.sumAddHom_apply, Finset, Finset.sum_subset, MultilinearMap, MultilinearMap.support_dfinsuppFamily_subset, classical, sumAddHom_apply, sum_subset, support_dfinsuppFamily_subset
-/
theorem fromDFinsuppEquiv_apply
    [Π i (j : κ i) (x : M i j), Decidable (x != 0)]
    (f : Π (p : Π i, κ i), MultilinearMap R (fun i => M i (p i)) N)
    (x : Π i, Π₀ (j : κ i), M i j) :
    fromDFinsuppEquiv κ R f x =
      ∑ p in Fintype.piFinset (fun i => (x i).support), f p (fun i => x i (p i)) := by
  classical
  refine (DFinsupp.sumAddHom_apply _ _).trans ?_
  refine Finset.sum_subset (MultilinearMap.support_dfinsuppFamily_subset _ _) ?_
  simp

@[simp]
/--
theorem `fromDFinsuppEquiv_symm_apply` / 定理 `fromDFinsuppEquiv_symm_apply`

English:
theorem fromDFinsuppEquiv_symm_apply
  statement: (f : MultilinearMap R (fun i => Π₀ j : κ i, M i j) N)
  proof: rfl

中文:
定理 fromDFinsuppEquiv_symm_apply
  结论: (f : 多重线性映射 R (fun i => Π₀ j : κ i, M i j) N)
  证明: rfl
-/
theorem fromDFinsuppEquiv_symm_apply (f : MultilinearMap R (fun i => Π₀ j : κ i, M i j) N)
    (p : Π i, κ i) :
    (fromDFinsuppEquiv κ R).symm f p = f.compLinearMap (fun i => DFinsupp.lsingle (p i)) :=
  rfl

end CommSemiring

end dfinsuppFamily

section freeDFinsuppEquiv

variable {ι' : Type*} [DecidableEq ι] [Fintype ι] [CommSemiring R]
  [forall i, Fintype (κ i)] [forall i, DecidableEq (κ i)]

/--
Definition of `freeDFinsuppEquiv` / `freeDFinsuppEquiv` 的定义

English:
definition freeDFinsuppEquiv
  signature: :
  body: (DFinsupp.domLCongr (M := fun _ => R) (Equiv.sigmaEquivProd _ _).symm) ≪≫ₗ
  (DFinsupp.sigmaCurryLEquiv (M := fun _ _ => R)) ≪≫ₗ
  DFinsupp.linearEquivFunOnFintype ≪≫ₗ
  LinearEquiv.piCongrRight (fun _ => MultilinearMap.piRingEquiv (ι := ι)) ≪≫ₗ
  fromDFinsuppEquiv κ R (M := fun _ _ => R)

中文:
定义 freeDFinsuppEquiv
  签名: :
  定义体: (DFinsupp.domLCongr (M := fun _ => R) (Equiv.sigmaEquivProd _ _).symm) ≪≫ₗ
  (DFinsupp.sigmaCurryLEquiv (M := fun _ _ => R)) ≪≫ₗ
  DFinsupp.linearEquivFunOnFintype ≪≫ₗ
  LinearEquiv.piCongrRight (fun _ => MultilinearMap.piRingEquiv (ι := ι)) ≪≫ₗ
  fromDFinsuppEquiv κ R (M := fun _ _ => R)

Depends on / 依赖: DFinsupp, DFinsupp.domLCongr, DFinsupp.linearEquivFunOnFintype, DFinsupp.sigmaCurryLEquiv, Equiv.sigmaEquivProd, LinearEquiv, LinearEquiv.piCongrRight, MultilinearMap, MultilinearMap.piRingEquiv, domLCongr, fromDFinsuppEquiv, linearEquivFunOnFintype, piCongrRight, piRingEquiv, sigmaCurryLEquiv, sigmaEquivProd
-/
def freeDFinsuppEquiv :
    (Π₀ (_ : (Π i, κ i) × ι'), R) ≃ₗ[R] MultilinearMap R (fun i => Π₀ _ : κ i, R) (Π₀ _ : ι', R) :=
  (DFinsupp.domLCongr (M := fun _ => R) (Equiv.sigmaEquivProd _ _).symm) ≪≫ₗ
  (DFinsupp.sigmaCurryLEquiv (M := fun _ _ => R)) ≪≫ₗ
  DFinsupp.linearEquivFunOnFintype ≪≫ₗ
  LinearEquiv.piCongrRight (fun _ => MultilinearMap.piRingEquiv (ι := ι)) ≪≫ₗ
  fromDFinsuppEquiv κ R (M := fun _ _ => R)

/--
theorem `freeDFinsuppEquiv_def` / 定理 `freeDFinsuppEquiv_def`

English:
theorem freeDFinsuppEquiv_def
  given: (f : Π₀ (_ : (Π i, κ i) × ι'), R)
  proof: rfl

中文:
定理 freeDFinsuppEquiv_def
  条件: (f : Π₀ (_ : (Π i, κ i) × ι'), R)
  证明: rfl
-/
theorem freeDFinsuppEquiv_def (f : Π₀ (_ : (Π i, κ i) × ι'), R) :
    freeDFinsuppEquiv f =
      fromDFinsuppEquiv κ R
      (LinearEquiv.piCongrRight (fun _ => MultilinearMap.piRingEquiv) <|
DFinsupp.linearEquivFunOnFintype (R := R)
DFinsupp.sigmaCurryLEquiv (R := R)
      (DFinsupp.domLCongr (R := R) (Equiv.sigmaEquivProd _ _).symm) f) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
When `freeDFinsuppEquiv` is applied to a map with a single value of one the resulting multilinear
map sends inputs to a single value in the codomain, taking a product over images from each
component of the domain.
-/
@[simp]
/--
theorem `freeDFinsuppEquiv_single` / 定理 `freeDFinsuppEquiv_single`

English:
theorem freeDFinsuppEquiv_single
  statement: [DecidableEq ι'] (p : (Π i, κ i) × ι') (r : R)
  proof: by
  classical
  conv_lhs => rw [← mul_one r, ← smul_eq_mul, DFinsupp.single_smul, map_smul, smul_apply]
  congr
  ext i
  obtain ⟨p, j⟩ := p
  rcases eq_or_ne j i with rfl | h
  · suffices forall (l : ι), (x l) (p l) = 0 -> 0 = ∏ i, (x i) (p i) by
      simpa [freeDFinsuppEquiv_def, MultilinearMap.

中文:
定理 freeDFinsuppEquiv_single
  结论: [DecidableEq ι'] (p : (Π i, κ i) × ι') (r : R)
  证明: by
  classical
  conv_lhs => rw [← mul_one r, ← smul_eq_mul, DFinsupp.single_smul, map_smul, smul_apply]
  congr
  ext i
  obtain ⟨p, j⟩ := p
  rcases eq_or_ne j i with rfl | h
  · suffices forall (l : ι), (x l) (p l) = 0 -> 0 = ∏ i, (x i) (p i) by
      simpa [freeDFinsuppEquiv_def, MultilinearMap.

Depends on / 依赖: DFinsupp, DFinsupp.sigmaCurryEquiv, DFinsupp.single_smul, Finset, Finset.mem_univ, Finset.prod_eq_zero, MultilinearMap, MultilinearMap.piRingEquiv, classical, conv_lhs, eq_or_ne, freeDFinsuppEquiv_def, fromDFinsuppEquiv_apply, map_smul, mem_univ, mul_one, piRingEquiv, prod_eq_zero, sigmaCurryEquiv, single_smul
-/
theorem freeDFinsuppEquiv_single [DecidableEq ι'] (p : (Π i, κ i) × ι') (r : R)
    (x : Π i, Π₀ _ : κ i, R) :
    freeDFinsuppEquiv (.single p r) x = r • .single p.2 ((∏ i, (x i) (p.1 i))) := by
  classical
  conv_lhs => rw [← mul_one r, ← smul_eq_mul, DFinsupp.single_smul, map_smul, smul_apply]
  congr
  ext i
  obtain ⟨p, j⟩ := p
  rcases eq_or_ne j i with rfl | h
  · suffices forall (l : ι), (x l) (p l) = 0 -> 0 = ∏ i, (x i) (p i) by
      simpa [freeDFinsuppEquiv_def, MultilinearMap.piRingEquiv, DFinsupp.sigmaCurryEquiv,
        fromDFinsuppEquiv_apply]
    exact fun i h => (Finset.prod_eq_zero (Finset.mem_univ i) h).symm
  · simp [freeDFinsuppEquiv_def, MultilinearMap.piRingEquiv, DFinsupp.sigmaCurryEquiv,
      fromDFinsuppEquiv_apply, h]

/--
theorem `freeDFinsuppEquiv_apply` / 定理 `freeDFinsuppEquiv_apply`

English:
theorem freeDFinsuppEquiv_apply
  statement: [DecidableEq ι'] [Fintype ι']
  proof: by
  apply DFinsupp.induction f
  · simp
  · rintro p r f - - hfx
    simp [Finset.sum_add_distrib, add_smul, hfx]

中文:
定理 freeDFinsuppEquiv_apply
  结论: [DecidableEq ι'] [有限类型 ι']
  证明: by
  apply DFinsupp.induction f
  · simp
  · rintro p r f - - hfx
    simp [Finset.sum_add_distrib, add_smul, hfx]

Depends on / 依赖: DFinsupp, DFinsupp.induction, Finset, Finset.sum_add_distrib, add_smul, sum_add_distrib
-/
theorem freeDFinsuppEquiv_apply [DecidableEq ι'] [Fintype ι']
    (f : Π₀ (_ : (Π i, κ i) × ι'), R) (x : Π i, Π₀ _ : κ i, R) :
    freeDFinsuppEquiv f x = ∑ p, f p • .single p.2 ((∏ i, (x i) (p.1 i))) := by
  apply DFinsupp.induction f
  · simp
  · rintro p r f - - hfx
    simp [Finset.sum_add_distrib, add_smul, hfx]

end freeDFinsuppEquiv

end MultilinearMap
