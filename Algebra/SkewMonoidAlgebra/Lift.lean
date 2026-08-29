/-
Copyright (c) 2025 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos Fernández, Xavier Généreux
-/
module

public import Mathlib.Algebra.SkewMonoidAlgebra.Basic
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.Algebra.Equiv

/-!
# Lemmas about different kinds of "lifts" to `SkewMonoidAlgebra`.
-/

@[expose] public section

noncomputable section

namespace SkewMonoidAlgebra

variable {k G H : Type*}

section lift

variable [CommSemiring k] [Monoid G] [Monoid H]
variable {A B : Type*} [Semiring A] [Algebra k A] [Semiring B] [Algebra k B]

/--
Definition of `liftNCAlgHom` / `liftNCAlgHom` 的定义

English:
definition liftNCAlgHom
  signature: [MulSemiringAction G A] [SMulCommClass G k A] (f : A ->ₐ[k] B)
  body: liftNCRingHom (f : A ->+* B) g h_comm
  commutes' := by simp [liftNCRingHom]

中文:
定义 liftNCAlgHom
  签名: [MulSemiring作用 G A] [标量交换类 G k A] (f : A ->ₐ[k] B)
  定义体: liftNCRingHom (f : A ->+* B) g h_comm
  commutes' := by simp [liftNCRingHom]

Depends on / 依赖: h_comm, liftNCRingHom
-/
def liftNCAlgHom [MulSemiringAction G A] [SMulCommClass G k A] (f : A ->ₐ[k] B)
    (g : G ->* B) (h_comm : forall {x y}, (f (y • x)) * g y = (g y) * (f x)) :
    SkewMonoidAlgebra A G ->ₐ[k] B where
  __ := liftNCRingHom (f : A ->+* B) g h_comm
  commutes' := by simp [liftNCRingHom]

/- Hypotheses needed for `k`-algebra homomorphism from `SkewMonoidAlgebra k G`-/
variable [MulSemiringAction G k] [SMulCommClass G k k]

variable (k G A)

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: : (G ->* A) ≃ (AlgHom k (SkewMonoidAlgebra k G) A) where
  body: (f : SkewMonoidAlgebra k G ->* A).comp (of k G)
  toFun F := by
    apply liftNCAlgHom (Algebra.ofId k A) F
    simp_rw [show forall (g : G) (r : k), g • r = r by
        exact fun _ _ => smul_algebraMap _ (algebraMap k k _)]
    exact Algebra.commutes _ _
  left_inv f := by
    ext
    simp [liftNC

中文:
定义 lift
  签名: : (G ->* A) ≃ (代数态射 k (斜幺半群代数 k G) A) where
  定义体: (f : SkewMonoidAlgebra k G ->* A).comp (of k G)
  toFun F := by
    apply liftNCAlgHom (Algebra.ofId k A) F
    simp_rw [show forall (g : G) (r : k), g • r = r by
        exact fun _ _ => smul_algebraMap _ (algebraMap k k _)]
    exact Algebra.commutes _ _
  left_inv f := by
    ext
    simp [liftNC

Depends on / 依赖: SkewMonoidAlgebra
-/
def lift : (G ->* A) ≃ (AlgHom k (SkewMonoidAlgebra k G) A) where
  invFun f := (f : SkewMonoidAlgebra k G ->* A).comp (of k G)
  toFun F := by
    apply liftNCAlgHom (Algebra.ofId k A) F
    simp_rw [show forall (g : G) (r : k), g • r = r by
        exact fun _ _ => smul_algebraMap _ (algebraMap k k _)]
    exact Algebra.commutes _ _
  left_inv f := by
    ext
    simp [liftNCAlgHom, liftNCRingHom]
  right_inv F := by
    ext
    simp [liftNCAlgHom, liftNCRingHom]

variable {k G A}

/--
theorem `lift_apply'` / 定理 `lift_apply'`

English:
theorem lift_apply'
  given: (F : G ->* A) (f : SkewMonoidAlgebra k G)
  proof: rfl

中文:
定理 lift_apply'
  条件: (F : G ->* A) (f : 斜幺半群代数 k G)
  证明: rfl
-/
theorem lift_apply' (F : G ->* A) (f : SkewMonoidAlgebra k G) :
    lift k G A F f = f.sum fun a b => algebraMap k A b * F a := rfl

/--
theorem `lift_apply` / 定理 `lift_apply`

English:
theorem lift_apply
  given: (F : G ->* A) (f : SkewMonoidAlgebra k G)
  proof: by simp [lift_apply', Algebra.smul_def]

中文:
定理 lift_apply
  条件: (F : G ->* A) (f : 斜幺半群代数 k G)
  证明: by simp [lift_apply', Algebra.smul_def]

Depends on / 依赖: Algebra, Algebra.smul_def, lift_apply, smul_def
-/
theorem lift_apply (F : G ->* A) (f : SkewMonoidAlgebra k G) :
    lift k G A F f = f.sum fun a b => b • F a := by simp [lift_apply', Algebra.smul_def]

/--
theorem `lift_def` / 定理 `lift_def`

English:
theorem lift_def
  given: (F : G ->* A)
  statement: (lift k G A F : SkewMonoidAlgebra k G -> A) =
  proof: rfl

@[simp]

中文:
定理 lift_def
  条件: (F : G ->* A)
  结论: (lift k G A F : 斜幺半群代数 k G -> A) =
  证明: rfl

@[simp]
-/
theorem lift_def (F : G ->* A) : (lift k G A F : SkewMonoidAlgebra k G -> A) =
    liftNC ((algebraMap k A : k ->+* A) : k ->+ A) F := rfl

@[simp]
/--
theorem `lift_symm_apply` / 定理 `lift_symm_apply`

English:
theorem lift_symm_apply
  given: (F : AlgHom k (SkewMonoidAlgebra k G) A) (x : G)
  proof: rfl

中文:
定理 lift_symm_apply
  条件: (F : 代数态射 k (斜幺半群代数 k G) A) (x : G)
  证明: rfl
-/
theorem lift_symm_apply (F : AlgHom k (SkewMonoidAlgebra k G) A) (x : G) :
    (lift k G A).symm F x = F (single x 1) := rfl

/--
theorem `lift_of` / 定理 `lift_of`

English:
theorem lift_of
  given: (F : G ->* A) (x)
  statement: lift k G A F (of k G x) = F x
  proof: by
  rw [of_apply]; rw [← lift_symm_apply]; rw [Equiv.symm_apply_apply]

@[simp]

中文:
定理 lift_of
  条件: (F : G ->* A) (x)
  结论: lift k G A F (of k G x) = F x
  证明: by
  rw [of_apply]; rw [← lift_symm_apply]; rw [Equiv.symm_apply_apply]

@[simp]

Depends on / 依赖: Equiv.symm_apply_apply, lift_symm_apply, of_apply, symm_apply_apply
-/
theorem lift_of (F : G ->* A) (x) : lift k G A F (of k G x) = F x := by
  rw [of_apply]; rw [← lift_symm_apply]; rw [Equiv.symm_apply_apply]

@[simp]
/--
theorem `lift_single` / 定理 `lift_single`

English:
theorem lift_single
  given: (F : G ->* A) (a b)
  statement: lift k G A F (single a b) = b • F a
  proof: by
  rw [lift_def]; rw [liftNC_single]; rw [Algebra.smul_def]; rw [AddMonoidHom.coe_coe]

中文:
定理 lift_single
  条件: (F : G ->* A) (a b)
  结论: lift k G A F (single a b) = b • F a
  证明: by
  rw [lift_def]; rw [liftNC_single]; rw [Algebra.smul_def]; rw [AddMonoidHom.coe_coe]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.coe_coe, Algebra, Algebra.smul_def, coe_coe, liftNC_single, lift_def, smul_def
-/
theorem lift_single (F : G ->* A) (a b) : lift k G A F (single a b) = b • F a := by
  rw [lift_def]; rw [liftNC_single]; rw [Algebra.smul_def]; rw [AddMonoidHom.coe_coe]

/--
theorem `lift_unique'` / 定理 `lift_unique'`

English:
theorem lift_unique'
  given: (F : AlgHom k (SkewMonoidAlgebra k G) A)
  proof: ((lift k G A).apply_symm_apply F).symm

中文:
定理 lift_unique'
  条件: (F : 代数态射 k (斜幺半群代数 k G) A)
  证明: ((lift k G A).apply_symm_apply F).symm

Depends on / 依赖: apply_symm_apply
-/
theorem lift_unique' (F : AlgHom k (SkewMonoidAlgebra k G) A) :
    F = lift k G A ((F : SkewMonoidAlgebra k G ->* A).comp (of k G)) :=
  ((lift k G A).apply_symm_apply F).symm

/--
theorem `lift_unique` / 定理 `lift_unique`

English:
theorem lift_unique
  statement: (F : AlgHom k (SkewMonoidAlgebra k G) A)
  proof: by
  conv_lhs =>
    rw [lift_unique' F]
    simp [lift_apply]

中文:
定理 lift_unique
  结论: (F : 代数态射 k (斜幺半群代数 k G) A)
  证明: by
  conv_lhs =>
    rw [lift_unique' F]
    simp [lift_apply]

Depends on / 依赖: conv_lhs, lift_apply, lift_unique
-/
theorem lift_unique (F : AlgHom k (SkewMonoidAlgebra k G) A)
    (f : SkewMonoidAlgebra k G) : F f = f.sum fun a b => b • F (single a 1) := by
  conv_lhs =>
    rw [lift_unique' F]
    simp [lift_apply]

/-- If `f : G → H` is a multiplicative homomorphism between two monoids, then
`mapDomain f` is an algebra homomorphism between their monoid algebras. -/
@[simps!]
/--
Definition of `mapDomainAlgHom` / `mapDomainAlgHom` 的定义

English:
definition mapDomainAlgHom
  signature: (k A : Type*) [CommSemiring k] [Semiring A] [Algebra k A] {H F : Type*}
  body: mapDomainRingHom hf
  commutes' := by simp [mapDomainRingHom]

中文:
定义 mapDomainAlgHom
  签名: (k A : 类型) [交换半环 k] [半环 A] [代数 k A] {H F : 类型}
  定义体: mapDomainRingHom hf
  commutes' := by simp [mapDomainRingHom]

Depends on / 依赖: mapDomainRingHom
-/
def mapDomainAlgHom (k A : Type*) [CommSemiring k] [Semiring A] [Algebra k A] {H F : Type*}
    [Monoid H] [FunLike F G H] [MonoidHomClass F G H] [MulSemiringAction G A]
    [MulSemiringAction H A] [SMulCommClass G k A] [SMulCommClass H k A] {f : F}
    (hf : forall (a : G) (x : A), a • x = (f a) • x) :
    SkewMonoidAlgebra A G ->ₐ[k] SkewMonoidAlgebra A H where
  __ := mapDomainRingHom hf
  commutes' := by simp [mapDomainRingHom]

end lift

section equivMapDomain

variable [AddCommMonoid k]

/-- Given `f : G ≃ H`, we can map `l : SkewMonoidAlgebra k G` to
`equivMapDomain f l : SkewMonoidAlgebra k H` (computably) by mapping the support forwards
and the function backwards. -/
@[simps]
/--
Definition of `equivMapDomain` / `equivMapDomain` 的定义

English:
definition equivMapDomain
  signature: (f : G ≃ H) (l : SkewMonoidAlgebra k G)
  body: l.coeff.equivMapDomain f

@[deprecated (since := "2026-07-06")] alias toFinsupp_equivMapDomain := coeff_equivMapDomain

中文:
定义 equivMapDomain
  签名: (f : G ≃ H) (l : 斜幺半群代数 k G)
  定义体: l.coeff.equivMapDomain f

@[deprecated (since := "2026-07-06")] alias toFinsupp_equivMapDomain := coeff_equivMapDomain

Depends on / 依赖: equivMapDomain, l.coeff.equivMapDomain
-/
def equivMapDomain (f : G ≃ H) (l : SkewMonoidAlgebra k G) : SkewMonoidAlgebra k H where
  coeff := l.coeff.equivMapDomain f

@[deprecated (since := "2026-07-06")] alias toFinsupp_equivMapDomain := coeff_equivMapDomain

/--
theorem `equivMapDomain_eq_mapDomain` / 定理 `equivMapDomain_eq_mapDomain`

English:
theorem equivMapDomain_eq_mapDomain
  given: (f : G ≃ H) (l : SkewMonoidAlgebra k G)
  proof: by
  apply coeff_injective
  ext x
  simp_rw [coeff_equivMapDomain, Finsupp.equivMapDomain_apply, coeff_mapDomain,
    Finsupp.mapDomain_equiv_apply]

中文:
定理 equivMapDomain_eq_mapDomain
  条件: (f : G ≃ H) (l : 斜幺半群代数 k G)
  证明: by
  apply coeff_injective
  ext x
  simp_rw [coeff_equivMapDomain, Finsupp.equivMapDomain_apply, coeff_mapDomain,
    Finsupp.mapDomain_equiv_apply]

Depends on / 依赖: Finsupp, Finsupp.equivMapDomain_apply, Finsupp.mapDomain_equiv_apply, coeff_equivMapDomain, coeff_injective, coeff_mapDomain, equivMapDomain_apply, mapDomain_equiv_apply, simp_rw
-/
theorem equivMapDomain_eq_mapDomain (f : G ≃ H) (l : SkewMonoidAlgebra k G) :
    equivMapDomain f l = mapDomain f l := by
  apply coeff_injective
  ext x
  simp_rw [coeff_equivMapDomain, Finsupp.equivMapDomain_apply, coeff_mapDomain,
    Finsupp.mapDomain_equiv_apply]

/--
theorem `equivMapDomain_trans` / 定理 `equivMapDomain_trans`

English:
theorem equivMapDomain_trans
  statement: {G' G'' : Type*} (f : G ≃ G') (g : G' ≃ G'')
  proof: by
  ext x; rfl

@[simp]

中文:
定理 equivMapDomain_trans
  结论: {G' G'' : 类型} (f : G ≃ G') (g : G' ≃ G'')
  证明: by
  ext x; rfl

@[simp]
-/
theorem equivMapDomain_trans {G' G'' : Type*} (f : G ≃ G') (g : G' ≃ G'')
    (l : SkewMonoidAlgebra k G) :
    equivMapDomain (f.trans g) l = equivMapDomain g (equivMapDomain f l) := by
  ext x; rfl

@[simp]
/--
theorem `equivMapDomain_refl` / 定理 `equivMapDomain_refl`

English:
theorem equivMapDomain_refl
  given: (l : SkewMonoidAlgebra k G)
  statement: equivMapDomain (Equiv.refl _) l = l
  proof: by
  ext x; rfl

@[simp]

中文:
定理 equivMapDomain_refl
  条件: (l : 斜幺半群代数 k G)
  结论: equivMapDomain (等价.refl _) l = l
  证明: by
  ext x; rfl

@[simp]
-/
theorem equivMapDomain_refl (l : SkewMonoidAlgebra k G) : equivMapDomain (Equiv.refl _) l = l := by
  ext x; rfl

@[simp]
/--
theorem `equivMapDomain_single` / 定理 `equivMapDomain_single`

English:
theorem equivMapDomain_single
  given: (f : G ≃ H) (a : G) (b : k)
  proof: by
  apply coeff_injective
  simp_rw [coeff_equivMapDomain, single, Finsupp.equivMapDomain_single]

中文:
定理 equivMapDomain_single
  条件: (f : G ≃ H) (a : G) (b : k)
  证明: by
  apply coeff_injective
  simp_rw [coeff_equivMapDomain, single, Finsupp.equivMapDomain_single]

Depends on / 依赖: Finsupp, Finsupp.equivMapDomain_single, coeff_equivMapDomain, coeff_injective, equivMapDomain_single, simp_rw, single
-/
theorem equivMapDomain_single (f : G ≃ H) (a : G) (b : k) :
    equivMapDomain f (single a b) = single (f a) b := by
  apply coeff_injective
  simp_rw [coeff_equivMapDomain, single, Finsupp.equivMapDomain_single]

end equivMapDomain

section domCongr

variable {A : Type*}

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- Given `AddCommMonoid A` and `e : G ≃ H`, `domCongr e` is the corresponding `Equiv` between
`SkewMonoidAlgebra A G` and `SkewMonoidAlgebra A H`. -/
@[simps apply]
/--
Definition of `domCongr` / `domCongr` 的定义

English:
definition domCongr
  signature: [AddCommMonoid A] (e : G ≃ H)
  body: equivMapDomain e
  invFun := equivMapDomain e.symm
  left_inv v := by simp [← equivMapDomain_trans]
  right_inv v := by simp [← equivMapDomain_trans]
  map_add' a b := by simp [equivMapDomain_eq_mapDomain, map_add]

中文:
定义 domCongr
  签名: [加法交换幺半群 A] (e : G ≃ H)
  定义体: equivMapDomain e
  invFun := equivMapDomain e.symm
  left_inv v := by simp [← equivMapDomain_trans]
  right_inv v := by simp [← equivMapDomain_trans]
  map_add' a b := by simp [equivMapDomain_eq_mapDomain, map_add]

Depends on / 依赖: equivMapDomain
-/
def domCongr [AddCommMonoid A] (e : G ≃ H) : SkewMonoidAlgebra A G ≃+ SkewMonoidAlgebra A H where
  toFun := equivMapDomain e
  invFun := equivMapDomain e.symm
  left_inv v := by simp [← equivMapDomain_trans]
  right_inv v := by simp [← equivMapDomain_trans]
  map_add' a b := by simp [equivMapDomain_eq_mapDomain, map_add]

/--
Definition of `domLCongr` / `domLCongr` 的定义

English:
definition domLCongr
  signature: [Semiring k] [AddCommMonoid A] [Module k A] (e : G ≃ H)
  body: (domCongr e : SkewMonoidAlgebra A G ≃+ SkewMonoidAlgebra A H).toLinearEquiv by
    simp only [domCongr_apply]
    intro c x
    simp_rw [equivMapDomain_eq_mapDomain, mapDomain_smul]

中文:
定义 domLCongr
  签名: [半环 k] [加法交换幺半群 A] [模 k A] (e : G ≃ H)
  定义体: (domCongr e : SkewMonoidAlgebra A G ≃+ SkewMonoidAlgebra A H).toLinearEquiv by
    simp only [domCongr_apply]
    intro c x
    simp_rw [equivMapDomain_eq_mapDomain, mapDomain_smul]

Depends on / 依赖: SkewMonoidAlgebra, domCongr, domCongr_apply, equivMapDomain_eq_mapDomain, mapDomain_smul, simp_rw, toLinearEquiv
-/
def domLCongr [Semiring k] [AddCommMonoid A] [Module k A] (e : G ≃ H) :
    SkewMonoidAlgebra A G ≃ₗ[k] SkewMonoidAlgebra A H :=
(domCongr e : SkewMonoidAlgebra A G ≃+ SkewMonoidAlgebra A H).toLinearEquiv by
    simp only [domCongr_apply]
    intro c x
    simp_rw [equivMapDomain_eq_mapDomain, mapDomain_smul]

variable (k A)

variable [Monoid G] [Monoid H] [Semiring A] [CommSemiring k] [Algebra k A] [MulSemiringAction G A]
  [MulSemiringAction H A] [SMulCommClass G k A] [SMulCommClass H k A]

/--
Definition of `domCongrAlg` / `domCongrAlg` 的定义

English:
definition domCongrAlg
  signature: {e : G ≃* H} (he : forall (a : G) (x : A), a • x = (e a) • x)
  body: AlgEquiv.ofLinearEquiv
    (domLCongr e : SkewMonoidAlgebra A G ≃ₗ[k] SkewMonoidAlgebra A H)
    ((equivMapDomain_eq_mapDomain _ _).trans <| mapDomain_one e)
    (fun f g => (equivMapDomain_eq_mapDomain _ _).trans <| (mapDomain_mul f g he).trans <|
        congr_arg₂ _ (equivMapDomain_eq_mapDomain _

中文:
定义 domCongrAlg
  签名: {e : G ≃* H} (he : 对任意 (a : G) (x : A), a • x = (e a) • x)
  定义体: AlgEquiv.ofLinearEquiv
    (domLCongr e : SkewMonoidAlgebra A G ≃ₗ[k] SkewMonoidAlgebra A H)
    ((equivMapDomain_eq_mapDomain _ _).trans <| mapDomain_one e)
    (fun f g => (equivMapDomain_eq_mapDomain _ _).trans <| (mapDomain_mul f g he).trans <|
        congr_arg₂ _ (equivMapDomain_eq_mapDomain _

Depends on / 依赖: AlgEquiv, AlgEquiv.ofLinearEquiv, SkewMonoidAlgebra, domLCongr, equivMapDomain_eq_mapDomain, mapDomain_mul, mapDomain_one, ofLinearEquiv
-/
def domCongrAlg {e : G ≃* H} (he : forall (a : G) (x : A), a • x = (e a) • x) :
    SkewMonoidAlgebra A G ≃ₐ[k] SkewMonoidAlgebra A H :=
  AlgEquiv.ofLinearEquiv
    (domLCongr e : SkewMonoidAlgebra A G ≃ₗ[k] SkewMonoidAlgebra A H)
    ((equivMapDomain_eq_mapDomain _ _).trans <| mapDomain_one e)
    (fun f g => (equivMapDomain_eq_mapDomain _ _).trans <| (mapDomain_mul f g he).trans <|
        congr_arg₂ _ (equivMapDomain_eq_mapDomain _ _).symm (equivMapDomain_eq_mapDomain _ _).symm)

/--
theorem `domCongrAlg_toAlgHom` / 定理 `domCongrAlg_toAlgHom`

English:
theorem domCongrAlg_toAlgHom
  given: {e : G ≃* H} (he : forall (a : G) (x : A), a • x = (e a) • x)
  proof: AlgHom.ext fun _ => equivMapDomain_eq_mapDomain _ _

中文:
定理 domCongrAlg_toAlgHom
  条件: {e : G ≃* H} (he : 对任意 (a : G) (x : A), a • x = (e a) • x)
  证明: AlgHom.ext fun _ => equivMapDomain_eq_mapDomain _ _

Depends on / 依赖: AlgHom, AlgHom.ext, equivMapDomain_eq_mapDomain
-/
theorem domCongrAlg_toAlgHom {e : G ≃* H} (he : forall (a : G) (x : A), a • x = (e a) • x) :
    (domCongrAlg k A he).toAlgHom = mapDomainAlgHom k A he :=
AlgHom.ext fun _ => equivMapDomain_eq_mapDomain _ _

/--
theorem `domCongrAlg_apply` / 定理 `domCongrAlg_apply`

English:
theorem domCongrAlg_apply
  statement: {e : G ≃* H} (he : forall (a : G) (x : A), a • x = (e a) • x)
  proof: rfl

中文:
定理 domCongrAlg_apply
  结论: {e : G ≃* H} (he : 对任意 (a : G) (x : A), a • x = (e a) • x)
  证明: rfl
-/
@[simp] theorem domCongrAlg_apply {e : G ≃* H} (he : forall (a : G) (x : A), a • x = (e a) • x)
    (f : SkewMonoidAlgebra A G) (h : H) : (domCongrAlg k A he f).coeff h = f.coeff (e.symm h) :=
  rfl

/--
theorem `domCongr_support` / 定理 `domCongr_support`

English:
theorem domCongr_support
  statement: {e : G ≃* H} (he : forall (a : G) (x : A), a • x = (e a) • x)
  proof: rfl

中文:
定理 domCongr_support
  结论: {e : G ≃* H} (he : 对任意 (a : G) (x : A), a • x = (e a) • x)
  证明: rfl
-/
@[simp] theorem domCongr_support {e : G ≃* H} (he : forall (a : G) (x : A), a • x = (e a) • x)
    (f : SkewMonoidAlgebra A G) : (domCongrAlg k A he f).support = f.support.map e :=
  rfl

/--
theorem `domCongr_single` / 定理 `domCongr_single`

English:
theorem domCongr_single
  statement: {e : G ≃* H} (he : forall (a : G) (x : A), a • x = (e a) • x)
  proof: equivMapDomain_single ..

中文:
定理 domCongr_single
  结论: {e : G ≃* H} (he : 对任意 (a : G) (x : A), a • x = (e a) • x)
  证明: equivMapDomain_single ..
-/
@[simp] theorem domCongr_single {e : G ≃* H} (he : forall (a : G) (x : A), a • x = (e a) • x)
    (g : G) (a : A) : domCongrAlg k A he (single g a) = single (e g) a :=
  equivMapDomain_single ..

/--
theorem `domCongr_refl` / 定理 `domCongr_refl`

English:
theorem domCongr_refl
  proof: by
  apply AlgEquiv.ext
  aesop

中文:
定理 domCongr_refl
  证明: by
  apply AlgEquiv.ext
  aesop

Depends on / 依赖: AlgEquiv, AlgEquiv.ext, AlgEquiv.refl, MulEquiv, MulEquiv.refl
-/
theorem domCongr_refl :
    domCongrAlg k A (e := MulEquiv.refl G) (fun _ _ => rfl) = AlgEquiv.refl := by
  apply AlgEquiv.ext
  aesop

/--
theorem `domCongr_symm` / 定理 `domCongr_symm`

English:
theorem domCongr_symm
  given: {e : G ≃* H} (he : forall (a : G) (x : A), a • x = (e a) • x)
  proof: rfl

中文:
定理 domCongr_symm
  条件: {e : G ≃* H} (he : 对任意 (a : G) (x : A), a • x = (e a) • x)
  证明: rfl
-/
@[simp] theorem domCongr_symm {e : G ≃* H} (he : forall (a : G) (x : A), a • x = (e a) • x) :
    (domCongrAlg k A he).symm =
      domCongrAlg (e := e.symm) _ _ (fun a x => by rw [he, MulEquiv.apply_symm_apply]) :=
  rfl

end domCongr

section Submodule

variable [Semiring k] [Monoid G] [MulSemiringAction G k]

variable {V : Type*} [AddCommMonoid V] [Module k V] [Module (SkewMonoidAlgebra k G) V]
  [IsScalarTower k (SkewMonoidAlgebra k G) V]

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
Definition of `submoduleOfSmulMem` / `submoduleOfSmulMem` 的定义

English:
definition submoduleOfSmulMem
  signature: (W : Submodule k V) (h : forall (g : G) (v : V), v in W -> of k G g • v in W)
  body: W
  zero_mem' := W.zero_mem'
  add_mem' := W.add_mem'
  smul_mem' := by
    intro f v hv
    rw [← sum_single f]; rw [sum_def]; rw [Finsupp.sum]; rw [Finset.sum_smul]
    simp_rw [← smul_of, smul_assoc]
    exact Submodule.sum_smul_mem W _ fun g _ => h g v hv

中文:
定义 submoduleOfSmulMem
  签名: (W : 子模 k V) (h : 对任意 (g : G) (v : V), v in W -> of k G g • v in W)
  定义体: W
  zero_mem' := W.zero_mem'
  add_mem' := W.add_mem'
  smul_mem' := by
    intro f v hv
    rw [← sum_single f]; rw [sum_def]; rw [Finsupp.sum]; rw [Finset.sum_smul]
    simp_rw [← smul_of, smul_assoc]
    exact Submodule.sum_smul_mem W _ fun g _ => h g v hv
-/
def submoduleOfSmulMem (W : Submodule k V) (h : forall (g : G) (v : V), v in W -> of k G g • v in W) :
    Submodule (SkewMonoidAlgebra k G) V where
  carrier := W
  zero_mem' := W.zero_mem'
  add_mem' := W.add_mem'
  smul_mem' := by
    intro f v hv
    rw [← sum_single f]; rw [sum_def]; rw [Finsupp.sum]; rw [Finset.sum_smul]
    simp_rw [← smul_of, smul_assoc]
    exact Submodule.sum_smul_mem W _ fun g _ => h g v hv

end Submodule

end SkewMonoidAlgebra
