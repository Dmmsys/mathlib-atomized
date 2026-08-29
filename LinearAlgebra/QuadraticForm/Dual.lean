/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
public import Mathlib.LinearAlgebra.QuadraticForm.Prod

/-!
# Quadratic form structures related to `Module.Dual`

## Main definitions

* `LinearMap.dualProd R M`, the bilinear form on `(f, x) : Module.Dual R M × M` defined as
  `f x`.
* `QuadraticForm.dualProd R M`, the quadratic form on `(f, x) : Module.Dual R M × M` defined as
  `f x`.
* `QuadraticForm.toDualProd : (Q.prod <| -Q) →qᵢ QuadraticForm.dualProd R M` a form-preserving map
  from `(Q.prod <| -Q)` to `QuadraticForm.dualProd R M`.

-/

@[expose] public section

variable (R M N : Type*)

namespace LinearMap

section Semiring

variable [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The symmetric bilinear form on `Module.Dual R M × M` defined as
`B (f, x) (g, y) = f y + g x`. -/
@[simps!]
/--
Definition of `dualProd` / `dualProd` 的定义

English:
definition dualProd
  signature: : LinearMap.BilinForm R (Module.Dual R M × M)
  body: (applyₗ.comp (snd R (Module.Dual R M) M)).compl₂ (fst R (Module.Dual R M) M) +
      ((applyₗ.comp (snd R (Module.Dual R M) M)).compl₂ (fst R (Module.Dual R M) M)).flip

中文:
定义 dualProd
  签名: : 线性映射.BilinForm R (模.对偶 R M × M)
  定义体: (applyₗ.comp (snd R (Module.Dual R M) M)).compl₂ (fst R (Module.Dual R M) M) +
      ((applyₗ.comp (snd R (Module.Dual R M) M)).compl₂ (fst R (Module.Dual R M) M)).flip

Depends on / 依赖: Module, Module.Dual
-/
def dualProd : LinearMap.BilinForm R (Module.Dual R M × M) :=
    (applyₗ.comp (snd R (Module.Dual R M) M)).compl₂ (fst R (Module.Dual R M) M) +
      ((applyₗ.comp (snd R (Module.Dual R M) M)).compl₂ (fst R (Module.Dual R M) M)).flip

/--
theorem `isSymm_dualProd` / 定理 `isSymm_dualProd`

English:
theorem isSymm_dualProd
  statement: (dualProd R M).IsSymm
  proof: ⟨fun _x _y => add_comm _ _⟩

中文:
定理 isSymm_dualProd
  结论: (dualProd R M).是Symm
  证明: ⟨fun _x _y => add_comm _ _⟩

Depends on / 依赖: add_comm
-/
theorem isSymm_dualProd : (dualProd R M).IsSymm := ⟨fun _x _y => add_comm _ _⟩

end Semiring

section Ring

variable [CommRing R] [AddCommGroup M] [Module R M]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `separatingLeft_dualProd` / 定理 `separatingLeft_dualProd`

English:
theorem separatingLeft_dualProd
  proof: by
  rw [separatingLeft_iff_ker_eq_bot]; rw [ker_eq_bot]
  let e := LinearEquiv.prodComm R _ _ ≪≫ₗ Module.dualProdDualEquivDual R (Module.Dual R M) M
  let h_d := e.symm.toLinearMap.comp (dualProd R M)
  refine (Function.Injective.of_comp_iff e.symm.injective
    (dualProd R M)).symm.trans ?_
  rw [

中文:
定理 separatingLeft_dualProd
  证明: by
  rw [separatingLeft_iff_ker_eq_bot]; rw [ker_eq_bot]
  let e := LinearEquiv.prodComm R _ _ ≪≫ₗ Module.dualProdDualEquivDual R (Module.Dual R M) M
  let h_d := e.symm.toLinearMap.comp (dualProd R M)
  refine (Function.Injective.of_comp_iff e.symm.injective
    (dualProd R M)).symm.trans ?_
  rw [

Depends on / 依赖: Function, Function.Injective, Function.Injective.of_comp_iff, Injective, LinearEquiv, LinearEquiv.coe_toLinearMap, LinearEquiv.prodComm, Module, Module.Dual, Module.Dual.eval, Module.dualProdDualEquivDual, Prod.ext, coe_comp, coe_toLinearMap, dualProd, dualProdDualEquivDual, e.symm.injective, e.symm.toLinearMap.comp, injective, ker_eq_bot
-/
theorem separatingLeft_dualProd :
    (dualProd R M).SeparatingLeft ↔ Function.Injective (Module.Dual.eval R M) := by
  rw [separatingLeft_iff_ker_eq_bot]; rw [ker_eq_bot]
  let e := LinearEquiv.prodComm R _ _ ≪≫ₗ Module.dualProdDualEquivDual R (Module.Dual R M) M
  let h_d := e.symm.toLinearMap.comp (dualProd R M)
  refine (Function.Injective.of_comp_iff e.symm.injective
    (dualProd R M)).symm.trans ?_
  rw [← LinearEquiv.coe_toLinearMap]; rw [← coe_comp]
  change Function.Injective h_d ↔ _
  have : h_d = prodMap id (Module.Dual.eval R M) := by
    refine ext fun x => Prod.ext ?_ ?_
    · ext
      dsimp [e, h_d, Module.Dual.eval, LinearEquiv.prodComm]
      simp
    · ext
      dsimp [e, h_d, Module.Dual.eval, LinearEquiv.prodComm]
      simp
  rw [this]; rw [coe_prodMap]
  refine Prod.map_injective.trans ?_
  exact and_iff_right Function.injective_id

end Ring

end LinearMap

open QuadraticMap

namespace QuadraticForm
section Semiring

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]

/-- The quadratic form on `Module.Dual R M × M` defined as `Q (f, x) = f x`. -/
@[simps]
/--
Definition of `dualProd` / `dualProd` 的定义

English:
definition dualProd
  signature: : QuadraticForm R (Module.Dual R M × M) where
  body: p.1 p.2
  toFun_smul a p := by
    rw [Prod.smul_fst]; rw [Prod.smul_snd]; rw [LinearMap.smul_apply]; rw [map_smul]; rw [smul_eq_mul]; rw [smul_eq_mul]; rw [smul_eq_mul]; rw [mul_assoc]
  exists_companion' :=
    ⟨LinearMap.dualProd R M, fun p q => by
      rw [LinearMap.dualProd_apply_apply]; rw [P

中文:
定义 dualProd
  签名: : QuadraticForm R (模.对偶 R M × M) where
  定义体: p.1 p.2
  toFun_smul a p := by
    rw [Prod.smul_fst]; rw [Prod.smul_snd]; rw [LinearMap.smul_apply]; rw [map_smul]; rw [smul_eq_mul]; rw [smul_eq_mul]; rw [smul_eq_mul]; rw [mul_assoc]
  exists_companion' :=
    ⟨LinearMap.dualProd R M, fun p q => by
      rw [LinearMap.dualProd_apply_apply]; rw [P
-/
def dualProd : QuadraticForm R (Module.Dual R M × M) where
  toFun p := p.1 p.2
  toFun_smul a p := by
    rw [Prod.smul_fst]; rw [Prod.smul_snd]; rw [LinearMap.smul_apply]; rw [map_smul]; rw [smul_eq_mul]; rw [smul_eq_mul]; rw [smul_eq_mul]; rw [mul_assoc]
  exists_companion' :=
    ⟨LinearMap.dualProd R M, fun p q => by
      rw [LinearMap.dualProd_apply_apply]; rw [Prod.fst_add]; rw [Prod.snd_add]; rw [LinearMap.add_apply]; rw [map_add]; rw [map_add]; rw [add_right_comm _ (q.1 q.2)]; rw [add_comm (q.1 p.2) (p.1 q.2)]; rw [← add_assoc]; rw [←
        add_assoc]⟩

@[simp]
/--
theorem `_root_.LinearMap.dualProd.toQuadraticForm` / 定理 `_root_.LinearMap.dualProd.toQuadraticForm`

English:
theorem _root_.LinearMap.dualProd.toQuadraticForm
  proof: ext fun _a => (two_nsmul _).symm

中文:
定理 _root_.线性映射.dualProd.toQuadraticForm
  证明: ext fun _a => (two_nsmul _).symm

Depends on / 依赖: two_nsmul
-/
theorem _root_.LinearMap.dualProd.toQuadraticForm :
    (LinearMap.dualProd R M).toQuadraticMap = 2 • dualProd R M :=
  ext fun _a => (two_nsmul _).symm

variable {R M N}

/-- Any module isomorphism induces a quadratic isomorphism between the corresponding `dual_prod.` -/
@[simps!]
/--
Definition of `dualProdIsometry` / `dualProdIsometry` 的定义

English:
definition dualProdIsometry
  signature: (f : M ≃ₗ[R] N)
  body: f.dualMap.symm.prodCongr f
map_app' x := DFunLike.congr_arg x.fst f.symm_apply_apply _

中文:
定义 dualProdIsometry
  签名: (f : M ≃ₗ[R] N)
  定义体: f.dualMap.symm.prodCongr f
map_app' x := DFunLike.congr_arg x.fst f.symm_apply_apply _

Depends on / 依赖: dualMap, f.dualMap.symm.prodCongr, prodCongr
-/
def dualProdIsometry (f : M ≃ₗ[R] N) : (dualProd R M).IsometryEquiv (dualProd R N) where
  toLinearEquiv := f.dualMap.symm.prodCongr f
map_app' x := DFunLike.congr_arg x.fst f.symm_apply_apply _

/-- `QuadraticForm.dualProd` commutes (isometrically) with `QuadraticForm.prod`. -/
@[simps!]
/--
Definition of `dualProdProdIsometry` / `dualProdProdIsometry` 的定义

English:
definition dualProdProdIsometry
  signature: :
  body: (Module.dualProdDualEquivDual R M N).symm.prodCongr (LinearEquiv.refl R (M × N)) ≪≫ₗ
      LinearEquiv.prodProdProdComm R _ _ M N
  map_app' m :=
(m.fst.map_add _ _).symm.trans DFunLike.congr_arg m.fst Prod.ext (add_zero _) (zero_add _)

中文:
定义 dualProdProdIsometry
  签名: :
  定义体: (Module.dualProdDualEquivDual R M N).symm.prodCongr (LinearEquiv.refl R (M × N)) ≪≫ₗ
      LinearEquiv.prodProdProdComm R _ _ M N
  map_app' m :=
(m.fst.map_add _ _).symm.trans DFunLike.congr_arg m.fst Prod.ext (add_zero _) (zero_add _)

Depends on / 依赖: DFunLike, DFunLike.congr_arg, LinearEquiv, LinearEquiv.prodProdProdComm, LinearEquiv.refl, Module, Module.dualProdDualEquivDual, Prod.ext, add_zero, congr_arg, dualProdDualEquivDual, m.fst, m.fst.map_add, map_add, map_app, prodCongr, prodProdProdComm, symm.prodCongr, symm.trans, zero_add
-/
def dualProdProdIsometry :
    (dualProd R (M × N)).IsometryEquiv ((dualProd R M).prod (dualProd R N)) where
  toLinearEquiv :=
    (Module.dualProdDualEquivDual R M N).symm.prodCongr (LinearEquiv.refl R (M × N)) ≪≫ₗ
      LinearEquiv.prodProdProdComm R _ _ M N
  map_app' m :=
(m.fst.map_add _ _).symm.trans DFunLike.congr_arg m.fst Prod.ext (add_zero _) (zero_add _)

end Semiring

section Ring

variable [CommRing R] [AddCommGroup M] [Module R M]
variable {R M}

set_option backward.defeqAttrib.useBackward true in
/-- The isometry sending `(Q.prod <| -Q)` to `(QuadraticForm.dualProd R M)`.

This is `σ` from Proposition 4.8, page 84 of
[*Hermitian K-Theory and Geometric Applications*][hyman1973]; though we swap the order of the pairs.
-/
@[simps!]
/--
Definition of `toDualProd` / `toDualProd` 的定义

English:
definition toDualProd
  signature: (Q : QuadraticForm R M) [Invertible (2 : R)]
  body: LinearMap.prod
    (Q.associated.comp (LinearMap.fst _ _ _) + Q.associated.comp (LinearMap.snd _ _ _))
    (LinearMap.fst _ _ _ - LinearMap.snd _ _ _)
  map_app' x := by
    dsimp only [QuadraticMap.associated, QuadraticMap.associatedHom]
    dsimp only [LinearMap.smul_apply, LinearMap.coe_mk, AddHo

中文:
定义 toDualProd
  签名: (Q : QuadraticForm R M) [可逆 (2 : R)]
  定义体: LinearMap.prod
    (Q.associated.comp (LinearMap.fst _ _ _) + Q.associated.comp (LinearMap.snd _ _ _))
    (LinearMap.fst _ _ _ - LinearMap.snd _ _ _)
  map_app' x := by
    dsimp only [QuadraticMap.associated, QuadraticMap.associatedHom]
    dsimp only [LinearMap.smul_apply, LinearMap.coe_mk, AddHo

Depends on / 依赖: LinearMap, LinearMap.prod
-/
def toDualProd (Q : QuadraticForm R M) [Invertible (2 : R)] :
    (Q.prod <| -Q) ->qᵢ QuadraticForm.dualProd R M where
  toLinearMap := LinearMap.prod
    (Q.associated.comp (LinearMap.fst _ _ _) + Q.associated.comp (LinearMap.snd _ _ _))
    (LinearMap.fst _ _ _ - LinearMap.snd _ _ _)
  map_app' x := by
    dsimp only [QuadraticMap.associated, QuadraticMap.associatedHom]
    dsimp only [LinearMap.smul_apply, LinearMap.coe_mk, AddHom.coe_mk, AddHom.toFun_eq_coe,
      LinearMap.coe_toAddHom, LinearMap.prod_apply, Function.prod_apply, LinearMap.add_apply,
      LinearMap.coe_comp, Function.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply,
      LinearMap.sub_apply, dualProd_apply, polarBilin_apply_apply, QuadraticMap.prod_apply]
    simp only [neg_apply, polar_sub_right, polar_self, nsmul_eq_mul, Nat.cast_ofNat,
      polar_comm _ x.1 x.2, smul_sub, Module.End.smul_def, sub_add_sub_cancel,
      ← sub_eq_add_neg (Q x.1) (Q x.2)]
    rw [← map_sub (⅟2 : Module.End R R)]; rw [← mul_sub]; rw [← Module.End.smul_def]
    simp only [Module.End.smul_def, half_moduleEnd_apply_eq_half_smul, smul_eq_mul,
      invOf_mul_cancel_left']

/-!
TODO: show that `QuadraticForm.toDualProd` is an `QuadraticForm.IsometryEquiv`
-/

end Ring

end QuadraticForm

/--
lemma `LinearMap.BilinForm.linearIndependent_of_pairwise_le_zero` / 引理 `LinearMap.BilinForm.linearIndependent_of_pairwise_le_zero`

English:
lemma LinearMap.BilinForm.linearIndependent_of_pairwise_le_zero
  statement: {ι R M : Type*}
  proof: by
  refine linearIndependent_iff'.mpr fun s c hc => ?_
  set x := ∑ i in s with 0 < c i, c i • v i with hx
  set y := ∑ i in s with 0 < -c i, (-c i) • v i with hy
  replace hc : x = y := by
    classical
    simp_rw [hx, hy, neg_smul, Finset.sum_neg_distrib, ← add_eq_zero_iff_eq_neg]
    rw [← hc];

中文:
引理 线性映射.BilinForm.linearIndependent_of_pairwise_le_zero
  结论: {ι R M : 类型}
  证明: by
  refine linearIndependent_iff'.mpr fun s c hc => ?_
  set x := ∑ i in s with 0 < c i, c i • v i with hx
  set y := ∑ i in s with 0 < -c i, (-c i) • v i with hy
  replace hc : x = y := by
    classical
    simp_rw [hx, hy, neg_smul, Finset.sum_neg_distrib, ← add_eq_zero_iff_eq_neg]
    rw [← hc];

Depends on / 依赖: Finset, Finset.disjoint_filter, Finset.mem_filter, Finset.mem_union, Finset.subset_iff, Finset.sum_neg_distrib, Finset.sum_subset, Finset.sum_union, add_eq_zero_iff_eq_neg, classical, contextual, disjoint_filter, eq_comm, linearIndependent_iff, mem_filter, mem_union, neg_smul, replace, simp_rw, subset_iff
-/
lemma LinearMap.BilinForm.linearIndependent_of_pairwise_le_zero {ι R M : Type*}
    [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup M] [Module R M]
    (B : LinearMap.BilinForm R M) (hB : B.toQuadraticMap.PosDef)
    (f : Module.Dual R M) (v : ι -> M)
    (hp : forall i, 0 < f (v i))
    (hn : Pairwise fun i j => B (v i) (v j) <= 0) :
    LinearIndependent R v := by
  refine linearIndependent_iff'.mpr fun s c hc => ?_
  set x := ∑ i in s with 0 < c i, c i • v i with hx
  set y := ∑ i in s with 0 < -c i, (-c i) • v i with hy
  replace hc : x = y := by
    classical
    simp_rw [hx, hy, neg_smul, Finset.sum_neg_distrib, ← add_eq_zero_iff_eq_neg]
    rw [← hc]; rw [← Finset.sum_union]; rw [Finset.sum_subset]
    · grind only [= Finset.subset_iff, = Finset.mem_union, = Finset.mem_filter]
    · simp +contextual [eq_comm (a := (0 : R))]
    · grind only [Finset.disjoint_filter]
  have hx₀ : x = 0 := by
    suffices B x y <= 0 by simpa [hc, ← hB.le_zero_iff, B.toQuadraticMap_apply]
    suffices 0 <= ∑ x in s with c x < 0, ∑ i in s with 0 < c i, c x * (c i * (B (v i)) (v x)) by
      simpa [hx, hy, map_neg, Finset.mul_sum]
    refine Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun j hj => ?_
    grind [Pairwise, mul_nonneg_iff, mul_nonpos_iff]
  have H (c : ι -> R) (h : ∑ i in s with 0 < c i, c i • v i = 0) (i : ι) (hi : i in s) : c i <= 0 := by
    have : ∑ i in s with 0 < c i, c i * f (v i) = 0 := by simpa using (congr(f $h))
    rw [Finset.sum_eq_zero_iff_of_nonneg (by grind [mul_nonneg])] at this
    by_contra! hi'
    have : 0 < c i * f (v i) := mul_pos hi' (hp i)
    grind
  replace hx (i : ι) (hi : i in s) : c i <= 0 := H _ (by grind) i hi
  replace hy (i : ι) (hi : i in s) : -c i <= 0 := H (-c ·) (by grind) i hi
  grind
