/-
Copyright (c) 2024 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
module

public import Mathlib.Algebra.FiveLemma
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.AdicCompletion.Exactness
public import Mathlib.RingTheory.Flat.Tensor

/-!

# Adic completion as tensor product

In this file we examine properties of the natural map

`AdicCompletion I R ⊗[R] M →ₗ[AdicCompletion I R] AdicCompletion I M`.

We show (in the `AdicCompletion` namespace):

- `ofTensorProduct_bijective_of_pi_of_fintype`: it is an isomorphism if `M = R^n`.
- `ofTensorProduct_surjective_of_finite`: it is surjective, if `M` is a finite `R`-module.
- `ofTensorProduct_bijective_of_finite_of_isNoetherian`: it is an isomorphism if `R` is Noetherian
  and `M` is a finite `R`-module.

As a corollary we obtain

- `flat_of_isNoetherian`: the adic completion of a Noetherian ring `R` is `R`-flat.

## TODO

- Show that `ofTensorProduct` is an isomorphism for any finite free `R`-module over an arbitrary
  ring. This is mostly composing with the isomorphism to `R^n` and checking that the diagram
  commutes.

-/

@[expose] public section

suppress_compilation

universe u v

variable {R : Type*} [CommRing R] (I : Ideal R)
variable (M : Type*) [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]

open TensorProduct

namespace AdicCompletion

/--
Definition of `ofTensorProduct` / `ofTensorProduct` 的定义

English:
definition ofTensorProduct
  signature: : AdicCompletion I R otimes[R] M ->ₗ[AdicCompletion I R] AdicCompletion I M
  body: TensorProduct.AlgebraTensorModule.lift
    { toFun r := LinearMap.lsmul (AdicCompletion I R) (AdicCompletion I M) r ∘ₗ of I M
      map_add' x y := by
        apply LinearMap.ext
        simp
      map_smul' r x := by
        apply LinearMap.ext
        simp [mul_smul] }

@[simp]

中文:
定义 ofTensorProduct
  签名: : AdicCompletion I R otimes[R] M ->ₗ[AdicCompletion I R] AdicCompletion I M
  定义体: TensorProduct.AlgebraTensorModule.lift
    { toFun r := LinearMap.lsmul (AdicCompletion I R) (AdicCompletion I M) r ∘ₗ of I M
      map_add' x y := by
        apply LinearMap.ext
        simp
      map_smul' r x := by
        apply LinearMap.ext
        simp [mul_smul] }

@[simp]

Depends on / 依赖: AdicCompletion, AlgebraTensorModule, LinearMap, LinearMap.ext, LinearMap.lsmul, TensorProduct, TensorProduct.AlgebraTensorModule.lift, map_add, map_smul, mul_smul
-/
def ofTensorProduct : AdicCompletion I R otimes[R] M ->ₗ[AdicCompletion I R] AdicCompletion I M :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun r := LinearMap.lsmul (AdicCompletion I R) (AdicCompletion I M) r ∘ₗ of I M
      map_add' x y := by
        apply LinearMap.ext
        simp
      map_smul' r x := by
        apply LinearMap.ext
        simp [mul_smul] }

@[simp]
/--
lemma `ofTensorProduct_tmul` / 引理 `ofTensorProduct_tmul`

English:
lemma ofTensorProduct_tmul
  given: (r : AdicCompletion I R) (x : M)
  proof: by
  rfl

中文:
引理 ofTensorProduct_tmul
  条件: (r : AdicCompletion I R) (x : M)
  证明: by
  rfl
-/
lemma ofTensorProduct_tmul (r : AdicCompletion I R) (x : M) :
    ofTensorProduct I M (r otimesₜ x) = r • of I M x := by
  rfl

variable {M} in
/--
lemma `ofTensorProduct_naturality` / 引理 `ofTensorProduct_naturality`

English:
lemma ofTensorProduct_naturality
  given: (f : M ->ₗ[R] N)
  proof: by
  ext
  simp

中文:
引理 ofTensorProduct_naturality
  条件: (f : M ->ₗ[R] N)
  证明: by
  ext
  simp
-/
lemma ofTensorProduct_naturality (f : M ->ₗ[R] N) :
    map I f ∘ₗ ofTensorProduct I M =
      ofTensorProduct I N ∘ₗ AlgebraTensorModule.map LinearMap.id f := by
  ext
  simp

section PiFintype

/-
In this section we show that `ofTensorProduct` is an isomorphism if `M = R^n`.
-/

variable (ι : Type*)

section DecidableEq

variable [Fintype ι] [DecidableEq ι]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `piEquivOfFintype_comp_ofTensorProduct_eq` / 引理 `piEquivOfFintype_comp_ofTensorProduct_eq`

English:
lemma piEquivOfFintype_comp_ofTensorProduct_eq
  proof: by
  ext i j k
  suffices h : (if j = i then 1 else 0) = (if j = i then 1 else 0 : AdicCompletion I R).val k by
    simpa [Pi.single_apply, -smul_eq_mul]
  split <;> simp

中文:
引理 piEquivOfFintype_comp_ofTensorProduct_eq
  证明: by
  ext i j k
  suffices h : (if j = i then 1 else 0) = (if j = i then 1 else 0 : AdicCompletion I R).val k by
    simpa [Pi.single_apply, -smul_eq_mul]
  split <;> simp
-/
private lemma piEquivOfFintype_comp_ofTensorProduct_eq :
    piEquivOfFintype I (fun _ : ι => R) ∘ₗ ofTensorProduct I (ι -> R) =
      (TensorProduct.piScalarRight R (AdicCompletion I R) (AdicCompletion I R) ι).toLinearMap := by
  ext i j k
  suffices h : (if j = i then 1 else 0) = (if j = i then 1 else 0 : AdicCompletion I R).val k by
    simpa [Pi.single_apply, -smul_eq_mul]
  split <;> simp

/-
import Mathlib.RingTheory.AdicCompletion.Algebra

variable {R : Type*} [CommRing R] (I : Ideal R) (ι : Type*) [Fintype ι] [DecidableEq ι]

-- `AdicCompletion.module` has type `Module X Y → Module (F X) (F Y)` so introduces
-- diamonds if `X = Y`.
example : AdicCompletion.module I = Semiring.toModule := by
  fail_if_success with_reducible_and_instances rfl
  rfl

example : ((AdicCompletion.module I).toSMul : SMul (AdicCompletion I R) (AdicCompletion I R)) =
    Semiring.toModule.toSMul := by
  fail_if_success with_reducible_and_instances rfl
  rfl
-/
set_option backward.isDefEq.respectTransparency false in
/--
lemma `ofTensorProduct_eq` / 引理 `ofTensorProduct_eq`

English:
lemma ofTensorProduct_eq
  proof: by
  rw [← piEquivOfFintype_comp_ofTensorProduct_eq I ι]; rw [← LinearMap.comp_assoc]
  simp

中文:
引理 ofTensorProduct_eq
  证明: by
  rw [← piEquivOfFintype_comp_ofTensorProduct_eq I ι]; rw [← LinearMap.comp_assoc]
  simp
-/
private lemma ofTensorProduct_eq :
    ofTensorProduct I (ι -> R) = (piEquivOfFintype I (ι := ι) (fun _ : ι => R)).symm.toLinearMap ∘ₗ
      (TensorProduct.piScalarRight R (AdicCompletion I R) (AdicCompletion I R) ι).toLinearMap := by
  rw [← piEquivOfFintype_comp_ofTensorProduct_eq I ι]; rw [← LinearMap.comp_assoc]
  simp

/--
Definition of `ofTensorProductInvOfPiFintype` / `ofTensorProductInvOfPiFintype` 的定义

English:
definition ofTensorProductInvOfPiFintype
  signature: :
  body: letI f := piEquivOfFintype I (fun _ : ι => R)
  letI g := (TensorProduct.piScalarRight R (AdicCompletion I R) (AdicCompletion I R) ι).symm
  f.trans g

中文:
定义 ofTensorProductInvOfPiFintype
  签名: :
  定义体: letI f := piEquivOfFintype I (fun _ : ι => R)
  letI g := (TensorProduct.piScalarRight R (AdicCompletion I R) (AdicCompletion I R) ι).symm
  f.trans g

Depends on / 依赖: AdicCompletion, TensorProduct, TensorProduct.piScalarRight, f.trans, piEquivOfFintype, piScalarRight
-/
def ofTensorProductInvOfPiFintype :
    AdicCompletion I (ι -> R) ≃ₗ[AdicCompletion I R] AdicCompletion I R otimes[R] (ι -> R) :=
  letI f := piEquivOfFintype I (fun _ : ι => R)
  letI g := (TensorProduct.piScalarRight R (AdicCompletion I R) (AdicCompletion I R) ι).symm
  f.trans g

/-
import Mathlib.RingTheory.AdicCompletion.Algebra

variable {R : Type*} [CommRing R] (I : Ideal R) (ι : Type*) [Fintype ι] [DecidableEq ι]

-- `AdicCompletion.module` has type `Module X Y → Module (F X) (F Y)` so introduces
-- diamonds if `X = Y`.
example : AdicCompletion.module I = Semiring.toModule := by
  fail_if_success with_reducible_and_instances rfl
  rfl

example : ((AdicCompletion.module I).toSMul : SMul (AdicCompletion I R) (AdicCompletion I R)) =
    Semiring.toModule.toSMul := by
  fail_if_success with_reducible_and_instances rfl
  rfl
-/
set_option backward.isDefEq.respectTransparency false in
/--
lemma `ofTensorProductInvOfPiFintype_comp_ofTensorProduct` / 引理 `ofTensorProductInvOfPiFintype_comp_ofTensorProduct`

English:
lemma ofTensorProductInvOfPiFintype_comp_ofTensorProduct
  proof: by
  dsimp only [ofTensorProductInvOfPiFintype]
  rw [LinearEquiv.coe_trans]; rw [LinearMap.comp_assoc]; rw [piEquivOfFintype_comp_ofTensorProduct_eq]
  simp

中文:
引理 ofTensorProductInvOfPiFintype_comp_ofTensorProduct
  证明: by
  dsimp only [ofTensorProductInvOfPiFintype]
  rw [LinearEquiv.coe_trans]; rw [LinearMap.comp_assoc]; rw [piEquivOfFintype_comp_ofTensorProduct_eq]
  simp

Depends on / 依赖: LinearEquiv, LinearEquiv.coe_trans, LinearMap, LinearMap.comp_assoc, coe_trans, comp_assoc, ofTensorProductInvOfPiFintype, piEquivOfFintype_comp_ofTensorProduct_eq
-/
lemma ofTensorProductInvOfPiFintype_comp_ofTensorProduct :
    ofTensorProductInvOfPiFintype I ι ∘ₗ ofTensorProduct I (ι -> R) = LinearMap.id := by
  dsimp only [ofTensorProductInvOfPiFintype]
  rw [LinearEquiv.coe_trans]; rw [LinearMap.comp_assoc]; rw [piEquivOfFintype_comp_ofTensorProduct_eq]
  simp

/-
import Mathlib.RingTheory.AdicCompletion.Algebra

variable {R : Type*} [CommRing R] (I : Ideal R) (ι : Type*) [Fintype ι] [DecidableEq ι]

-- `AdicCompletion.module` has type `Module X Y → Module (F X) (F Y)` so introduces
-- diamonds if `X = Y`.
example : AdicCompletion.module I = Semiring.toModule := by
  fail_if_success with_reducible_and_instances rfl
  rfl

example : ((AdicCompletion.module I).toSMul : SMul (AdicCompletion I R) (AdicCompletion I R)) =
    Semiring.toModule.toSMul := by
  fail_if_success with_reducible_and_instances rfl
  rfl
-/
set_option backward.isDefEq.respectTransparency false in
/--
lemma `ofTensorProduct_comp_ofTensorProductInvOfPiFintype` / 引理 `ofTensorProduct_comp_ofTensorProductInvOfPiFintype`

English:
lemma ofTensorProduct_comp_ofTensorProductInvOfPiFintype
  proof: by
  dsimp only [ofTensorProductInvOfPiFintype]
  rw [LinearEquiv.coe_trans]; rw [ofTensorProduct_eq]; rw [LinearMap.comp_assoc]
  nth_rw 2 [← LinearMap.comp_assoc]
  simp

中文:
引理 ofTensorProduct_comp_ofTensorProductInvOfPiFintype
  证明: by
  dsimp only [ofTensorProductInvOfPiFintype]
  rw [LinearEquiv.coe_trans]; rw [ofTensorProduct_eq]; rw [LinearMap.comp_assoc]
  nth_rw 2 [← LinearMap.comp_assoc]
  simp

Depends on / 依赖: LinearEquiv, LinearEquiv.coe_trans, LinearMap, LinearMap.comp_assoc, coe_trans, comp_assoc, nth_rw, ofTensorProductInvOfPiFintype, ofTensorProduct_eq
-/
lemma ofTensorProduct_comp_ofTensorProductInvOfPiFintype :
    ofTensorProduct I (ι -> R) ∘ₗ ofTensorProductInvOfPiFintype I ι = LinearMap.id := by
  dsimp only [ofTensorProductInvOfPiFintype]
  rw [LinearEquiv.coe_trans]; rw [ofTensorProduct_eq]; rw [LinearMap.comp_assoc]
  nth_rw 2 [← LinearMap.comp_assoc]
  simp

/--
Definition of `ofTensorProductEquivOfPiFintype` / `ofTensorProductEquivOfPiFintype` 的定义

English:
definition ofTensorProductEquivOfPiFintype
  signature: :
  body: LinearEquiv.ofLinearMap
    (ofTensorProduct I (ι -> R))
    (ofTensorProductInvOfPiFintype I ι)
    (ofTensorProduct_comp_ofTensorProductInvOfPiFintype I ι)
    (ofTensorProductInvOfPiFintype_comp_ofTensorProduct I ι)

中文:
定义 ofTensorProductEquivOfPiFintype
  签名: :
  定义体: LinearEquiv.ofLinearMap
    (ofTensorProduct I (ι -> R))
    (ofTensorProductInvOfPiFintype I ι)
    (ofTensorProduct_comp_ofTensorProductInvOfPiFintype I ι)
    (ofTensorProductInvOfPiFintype_comp_ofTensorProduct I ι)

Depends on / 依赖: LinearEquiv, LinearEquiv.ofLinearMap, ofLinearMap, ofTensorProduct, ofTensorProductInvOfPiFintype, ofTensorProductInvOfPiFintype_comp_ofTensorProduct, ofTensorProduct_comp_ofTensorProductInvOfPiFintype
-/
def ofTensorProductEquivOfPiFintype :
    AdicCompletion I R otimes[R] (ι -> R) ≃ₗ[AdicCompletion I R] AdicCompletion I (ι -> R) :=
  LinearEquiv.ofLinearMap
    (ofTensorProduct I (ι -> R))
    (ofTensorProductInvOfPiFintype I ι)
    (ofTensorProduct_comp_ofTensorProductInvOfPiFintype I ι)
    (ofTensorProductInvOfPiFintype_comp_ofTensorProduct I ι)

end DecidableEq

/--
lemma `ofTensorProduct_bijective_of_pi_of_fintype` / 引理 `ofTensorProduct_bijective_of_pi_of_fintype`

English:
lemma ofTensorProduct_bijective_of_pi_of_fintype
  given: [Finite ι]
  proof: by
  classical
  cases nonempty_fintype ι
  exact EquivLike.bijective (ofTensorProductEquivOfPiFintype I ι)

中文:
引理 ofTensorProduct_bijective_of_pi_of_fintype
  条件: [Finite ι]
  证明: by
  classical
  cases nonempty_fintype ι
  exact EquivLike.bijective (ofTensorProductEquivOfPiFintype I ι)

Depends on / 依赖: EquivLike, EquivLike.bijective, bijective, classical, nonempty_fintype, ofTensorProductEquivOfPiFintype
-/
lemma ofTensorProduct_bijective_of_pi_of_fintype [Finite ι] :
    Function.Bijective (ofTensorProduct I (ι -> R)) := by
  classical
  cases nonempty_fintype ι
  exact EquivLike.bijective (ofTensorProductEquivOfPiFintype I ι)

end PiFintype

/--
lemma `ofTensorProduct_surjective_of_finite` / 引理 `ofTensorProduct_surjective_of_finite`

English:
lemma ofTensorProduct_surjective_of_finite
  given: [Module.Finite R M]
  proof: by
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R M
  let f := ofTensorProduct I M ∘ₗ p.baseChange (AdicCompletion I R)
  let g := map I p ∘ₗ ofTensorProduct I (Fin n -> R)
  have hfg : f = g := by
    ext
    simp [f, g]
  have hf : Function.Surjective f := by
    simp only [hfg, LinearMap.coe_

中文:
引理 ofTensorProduct_surjective_of_finite
  条件: [Module.Finite R M]
  证明: by
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R M
  let f := ofTensorProduct I M ∘ₗ p.baseChange (AdicCompletion I R)
  let g := map I p ∘ₗ ofTensorProduct I (Fin n -> R)
  have hfg : f = g := by
    ext
    simp [f, g]
  have hf : Function.Surjective f := by
    simp only [hfg, LinearMap.coe_

Depends on / 依赖: AdicCompletion, AdicCompletion.map_surjective, Finite, Function, Function.Surjective, Function.Surjective.comp, Function.Surjective.of_comp, LinearMap, LinearMap.coe_comp, Module, Module.Finite.exists_fin, Surjective, baseChange, coe_comp, exists_fin, map_surjective, ofTensorProduct, ofTensorProduct_bijective_of_pi_of_fintype, of_comp, p.baseChange
-/
lemma ofTensorProduct_surjective_of_finite [Module.Finite R M] :
    Function.Surjective (ofTensorProduct I M) := by
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R M
  let f := ofTensorProduct I M ∘ₗ p.baseChange (AdicCompletion I R)
  let g := map I p ∘ₗ ofTensorProduct I (Fin n -> R)
  have hfg : f = g := by
    ext
    simp [f, g]
  have hf : Function.Surjective f := by
    simp only [hfg, LinearMap.coe_comp, g]
    apply Function.Surjective.comp
    · exact AdicCompletion.map_surjective I hp
    · exact (ofTensorProduct_bijective_of_pi_of_fintype I (Fin n)).surjective
  exact Function.Surjective.of_comp hf

section Noetherian

variable {R : Type u} [CommRing R] (I : Ideal R)
variable (M : Type u) [AddCommGroup M] [Module R M]

/-!

### Noetherian case

Suppose `R` is Noetherian. Then we show that the canonical map
`AdicCompletion I R ⊗[R] M →ₗ[AdicCompletion I R] AdicCompletion I M` is an isomorphism for every
finite `R`-module `M`.

The strategy is the following: Choose a surjection `f : (ι → R) →ₗ[R] M` and consider the following
commutative diagram:

```
 AdicCompletion I R ⊗[R] ker f -→ AdicCompletion I R ⊗[R] (ι → R) -→ AdicCompletion I R ⊗[R] M -→ 0
               | | | |
               ↓ ↓ ↓ ↓
    AdicCompletion I (ker f) ------→ AdicCompletion I (ι → R) -------→ AdicCompletion I M ------→ 0
```

The vertical maps are given by `ofTensorProduct`. By the previous section we know that the second
vertical map is an isomorphism. Since `R` is Noetherian, `ker f` is finitely-generated, so again
by the previous section the first vertical map is surjective.

Moreover, both rows are exact by right-exactness of the tensor product and exactness of adic
completions over Noetherian rings. Hence we conclude by the 5-lemma.

-/

open CategoryTheory

section

variable {ι : Type} (f : (ι -> R) ->ₗ[R] M)

/-- The first horizontal arrow in the top row. -/
private
/--
Definition of `lTensorKerIncl` / `lTensorKerIncl` 的定义

English:
definition lTensorKerIncl
  signature: : AdicCompletion I R otimes[R] LinearMap.ker f ->ₗ[AdicCompletion I R]
  body: AlgebraTensorModule.map LinearMap.id (LinearMap.ker f).subtype

中文:
定义 lTensorKerIncl
  签名: : AdicCompletion I R otimes[R] LinearMap.ker f ->ₗ[AdicCompletion I R]
  定义体: AlgebraTensorModule.map LinearMap.id (LinearMap.ker f).subtype

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.map, LinearMap, LinearMap.id, LinearMap.ker, subtype
-/
def lTensorKerIncl : AdicCompletion I R otimes[R] LinearMap.ker f ->ₗ[AdicCompletion I R]
    AdicCompletion I R otimes[R] (ι -> R) :=
  AlgebraTensorModule.map LinearMap.id (LinearMap.ker f).subtype

/--
Definition of `lTensorf` / `lTensorf` 的定义

English:
definition lTensorf
  signature: :
  body: AlgebraTensorModule.map LinearMap.id f

中文:
定义 lTensorf
  签名: :
  定义体: AlgebraTensorModule.map LinearMap.id f
-/
private def lTensorf :
    AdicCompletion I R otimes[R] (ι -> R) ->ₗ[AdicCompletion I R] AdicCompletion I R otimes[R] M :=
  AlgebraTensorModule.map LinearMap.id f

variable (hf : Function.Surjective f)

include hf

/--
lemma `tens_exact` / 引理 `tens_exact`

English:
lemma tens_exact
  statement: Function.Exact (lTensorKerIncl I M f) (lTensorf I M f)
  proof: lTensor_exact (AdicCompletion I R) (f.exact_subtype_ker_map) hf

中文:
引理 tens_exact
  结论: Function.Exact (lTensorKerIncl I M f) (lTensorf I M f)
  证明: lTensor_exact (AdicCompletion I R) (f.exact_subtype_ker_map) hf
-/
private lemma tens_exact : Function.Exact (lTensorKerIncl I M f) (lTensorf I M f) :=
  lTensor_exact (AdicCompletion I R) (f.exact_subtype_ker_map) hf

/--
lemma `tens_surj` / 引理 `tens_surj`

English:
lemma tens_surj
  statement: Function.Surjective (lTensorf I M f)
  proof: LinearMap.lTensor_surjective (AdicCompletion I R) hf

中文:
引理 tens_surj
  结论: Function.Surjective (lTensorf I M f)
  证明: LinearMap.lTensor_surjective (AdicCompletion I R) hf
-/
private lemma tens_surj : Function.Surjective (lTensorf I M f) :=
  LinearMap.lTensor_surjective (AdicCompletion I R) hf

/--
lemma `adic_exact` / 引理 `adic_exact`

English:
lemma adic_exact
  given: [IsNoetherianRing R] [Finite ι]
  proof: map_exact (Submodule.injective_subtype _) (f.exact_subtype_ker_map) hf

中文:
引理 adic_exact
  条件: [IsNoetherianRing R] [Finite ι]
  证明: map_exact (Submodule.injective_subtype _) (f.exact_subtype_ker_map) hf
-/
private lemma adic_exact [IsNoetherianRing R] [Finite ι] :
    Function.Exact (map I (LinearMap.ker f).subtype) (map I f) :=
  map_exact (Submodule.injective_subtype _) (f.exact_subtype_ker_map) hf

/--
lemma `adic_surj` / 引理 `adic_surj`

English:
lemma adic_surj
  statement: Function.Surjective (map I f)
  proof: map_surjective I hf

private

中文:
引理 adic_surj
  结论: Function.Surjective (map I f)
  证明: map_surjective I hf

private
-/
private lemma adic_surj : Function.Surjective (map I f) :=
  map_surjective I hf

private
/--
lemma `ofTensorProduct_bijective_of_map_from_fin` / 引理 `ofTensorProduct_bijective_of_map_from_fin`

English:
lemma ofTensorProduct_bijective_of_map_from_fin
  given: [Finite ι] [IsNoetherianRing R]
  proof: LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective
    (lTensorKerIncl I M f)
    (lTensorf I M f)
    (0 : AdicCompletion I R otimes[R] M ->ₗ[AdicCompletion I R] Unit)
    (0 : _ ->ₗ[AdicCompletion I R] Unit)
    (map I <| (LinearMap.ker f).subtype)
    (map I f)
    (0 : _ ->

中文:
引理 ofTensorProduct_bijective_of_map_from_fin
  条件: [Finite ι] [IsNoetherianRing R]
  证明: LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective
    (lTensorKerIncl I M f)
    (lTensorf I M f)
    (0 : AdicCompletion I R otimes[R] M ->ₗ[AdicCompletion I R] Unit)
    (0 : _ ->ₗ[AdicCompletion I R] Unit)
    (map I <| (LinearMap.ker f).subtype)
    (map I f)
    (0 : _ ->

Depends on / 依赖: AdicCompletion, LinearMap, LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective, LinearMap.ker, bijective_of_surjective_of_bijective_of_bijective_of_injective, lTensorKerIncl, lTensorf, ofTensorP, ofTensorProduct, ofTensorProduct_naturality, otimes, subtype
-/
lemma ofTensorProduct_bijective_of_map_from_fin [Finite ι] [IsNoetherianRing R] :
    Function.Bijective (ofTensorProduct I M) :=
  LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective
    (lTensorKerIncl I M f)
    (lTensorf I M f)
    (0 : AdicCompletion I R otimes[R] M ->ₗ[AdicCompletion I R] Unit)
    (0 : _ ->ₗ[AdicCompletion I R] Unit)
    (map I <| (LinearMap.ker f).subtype)
    (map I f)
    (0 : _ ->ₗ[AdicCompletion I R] Unit)
    (0 : _ ->ₗ[AdicCompletion I R] Unit)
    (ofTensorProduct I (LinearMap.ker f))
    (ofTensorProduct I (ι -> R))
    (ofTensorProduct I M)
    0
    0
    (ofTensorProduct_naturality I <| (LinearMap.ker f).subtype)
    (ofTensorProduct_naturality I f)
    rfl
    rfl
    (tens_exact I M f hf)
    ((LinearMap.exact_zero_iff_surjective _ _).mpr <| tens_surj I M f hf)
    ((LinearMap.exact_zero_iff_surjective _ _).mpr <| Function.surjective_to_subsingleton _)
    (adic_exact I M f hf)
    ((LinearMap.exact_zero_iff_surjective _ _).mpr <| adic_surj I M f hf)
    ((LinearMap.exact_zero_iff_surjective _ _).mpr <| Function.surjective_to_subsingleton _)
    (ofTensorProduct_surjective_of_finite I (LinearMap.ker f))
    (ofTensorProduct_bijective_of_pi_of_fintype I ι)
    (Function.bijective_of_subsingleton _)
    (Function.injective_of_subsingleton _)

end

variable [IsNoetherianRing R]

/--
theorem `ofTensorProduct_bijective_of_finite_of_isNoetherian` / 定理 `ofTensorProduct_bijective_of_finite_of_isNoetherian`

English:
theorem ofTensorProduct_bijective_of_finite_of_isNoetherian
  proof: by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  exact ofTensorProduct_bijective_of_map_from_fin I M f hf

中文:
定理 ofTensorProduct_bijective_of_finite_of_isNoetherian
  证明: by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  exact ofTensorProduct_bijective_of_map_from_fin I M f hf

Depends on / 依赖: Finite, Module, Module.Finite.exists_fin, exists_fin, ofTensorProduct_bijective_of_map_from_fin
-/
theorem ofTensorProduct_bijective_of_finite_of_isNoetherian
    [Module.Finite R M] :
    Function.Bijective (ofTensorProduct I M) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  exact ofTensorProduct_bijective_of_map_from_fin I M f hf

/--
Definition of `ofTensorProductEquivOfFiniteNoetherian` / `ofTensorProductEquivOfFiniteNoetherian` 的定义

English:
definition ofTensorProductEquivOfFiniteNoetherian
  signature: [Module.Finite R M]
  body: LinearEquiv.ofBijective (ofTensorProduct I M)
    (ofTensorProduct_bijective_of_finite_of_isNoetherian I M)

中文:
定义 ofTensorProductEquivOfFiniteNoetherian
  签名: [Module.Finite R M]
  定义体: LinearEquiv.ofBijective (ofTensorProduct I M)
    (ofTensorProduct_bijective_of_finite_of_isNoetherian I M)

Depends on / 依赖: LinearEquiv, LinearEquiv.ofBijective, ofBijective, ofTensorProduct, ofTensorProduct_bijective_of_finite_of_isNoetherian
-/
def ofTensorProductEquivOfFiniteNoetherian [Module.Finite R M] :
    AdicCompletion I R otimes[R] M ≃ₗ[AdicCompletion I R] AdicCompletion I M :=
  LinearEquiv.ofBijective (ofTensorProduct I M)
    (ofTensorProduct_bijective_of_finite_of_isNoetherian I M)

/--
lemma `coe_ofTensorProductEquivOfFiniteNoetherian` / 引理 `coe_ofTensorProductEquivOfFiniteNoetherian`

English:
lemma coe_ofTensorProductEquivOfFiniteNoetherian
  given: [Module.Finite R M]
  proof: rfl

@[simp]

中文:
引理 coe_ofTensorProductEquivOfFiniteNoetherian
  条件: [Module.Finite R M]
  证明: rfl

@[simp]
-/
lemma coe_ofTensorProductEquivOfFiniteNoetherian [Module.Finite R M] :
    ofTensorProductEquivOfFiniteNoetherian I M = ofTensorProduct I M :=
  rfl

@[simp]
/--
lemma `ofTensorProductEquivOfFiniteNoetherian_apply` / 引理 `ofTensorProductEquivOfFiniteNoetherian_apply`

English:
lemma ofTensorProductEquivOfFiniteNoetherian_apply
  statement: [Module.Finite R M]
  proof: rfl

@[simp]

中文:
引理 ofTensorProductEquivOfFiniteNoetherian_apply
  结论: [Module.Finite R M]
  证明: rfl

@[simp]
-/
lemma ofTensorProductEquivOfFiniteNoetherian_apply [Module.Finite R M]
    (x : AdicCompletion I R otimes[R] M) :
    ofTensorProductEquivOfFiniteNoetherian I M x = ofTensorProduct I M x :=
  rfl

@[simp]
/--
lemma `ofTensorProductEquivOfFiniteNoetherian_symm_of` / 引理 `ofTensorProductEquivOfFiniteNoetherian_symm_of`

English:
lemma ofTensorProductEquivOfFiniteNoetherian_symm_of
  proof: by
  have h : (of I M) x = ofTensorProductEquivOfFiniteNoetherian I M (1 otimesₜ x) := by
    simp
  rw [h]; rw [LinearEquiv.symm_apply_apply]

中文:
引理 ofTensorProductEquivOfFiniteNoetherian_symm_of
  证明: by
  have h : (of I M) x = ofTensorProductEquivOfFiniteNoetherian I M (1 otimesₜ x) := by
    simp
  rw [h]; rw [LinearEquiv.symm_apply_apply]

Depends on / 依赖: LinearEquiv, LinearEquiv.symm_apply_apply, ofTensorProductEquivOfFiniteNoetherian, symm_apply_apply
-/
lemma ofTensorProductEquivOfFiniteNoetherian_symm_of
    [Module.Finite R M] (x : M) :
    (ofTensorProductEquivOfFiniteNoetherian I M).symm ((of I M) x) = 1 otimesₜ x := by
  have h : (of I M) x = ofTensorProductEquivOfFiniteNoetherian I M (1 otimesₜ x) := by
    simp
  rw [h]; rw [LinearEquiv.symm_apply_apply]

section

variable {M : Type u} [AddCommGroup M] [Module R M]
variable {N : Type u} [AddCommGroup N] [Module R N] (f : M ->ₗ[R] N)
variable [Module.Finite R M] [Module.Finite R N]

/--
lemma `tensor_map_id_left_eq_map` / 引理 `tensor_map_id_left_eq_map`

English:
lemma tensor_map_id_left_eq_map
  proof: by
  rw [coe_ofTensorProductEquivOfFiniteNoetherian]; rw [ofTensorProduct_naturality I f]
  ext x
  simp

中文:
引理 tensor_map_id_left_eq_map
  证明: by
  rw [coe_ofTensorProductEquivOfFiniteNoetherian]; rw [ofTensorProduct_naturality I f]
  ext x
  simp

Depends on / 依赖: coe_ofTensorProductEquivOfFiniteNoetherian, ofTensorProduct_naturality
-/
lemma tensor_map_id_left_eq_map :
    (AlgebraTensorModule.map LinearMap.id f) =
      (ofTensorProductEquivOfFiniteNoetherian I N).symm.toLinearMap ∘ₗ
      map I f ∘ₗ
      (ofTensorProductEquivOfFiniteNoetherian I M).toLinearMap := by
  rw [coe_ofTensorProductEquivOfFiniteNoetherian]; rw [ofTensorProduct_naturality I f]
  ext x
  simp

variable {f}

/--
lemma `tensor_map_id_left_injective_of_injective` / 引理 `tensor_map_id_left_injective_of_injective`

English:
lemma tensor_map_id_left_injective_of_injective
  given: (hf : Function.Injective f)
  proof: by
  rw [tensor_map_id_left_eq_map I f]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, EmbeddingLike.comp_injective,
    EquivLike.injective_comp]
  exact map_injective I hf

中文:
引理 tensor_map_id_left_injective_of_injective
  条件: (hf : Function.Injective f)
  证明: by
  rw [tensor_map_id_left_eq_map I f]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, EmbeddingLike.comp_injective,
    EquivLike.injective_comp]
  exact map_injective I hf

Depends on / 依赖: EmbeddingLike, EmbeddingLike.comp_injective, EquivLike, EquivLike.injective_comp, LinearEquiv, LinearEquiv.coe_coe, LinearMap, LinearMap.coe_comp, coe_coe, coe_comp, comp_injective, injective_comp, map_injective, tensor_map_id_left_eq_map
-/
lemma tensor_map_id_left_injective_of_injective (hf : Function.Injective f) :
    Function.Injective (AlgebraTensorModule.map LinearMap.id f :
        AdicCompletion I R otimes[R] M ->ₗ[AdicCompletion I R] AdicCompletion I R otimes[R] N) := by
  rw [tensor_map_id_left_eq_map I f]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, EmbeddingLike.comp_injective,
    EquivLike.injective_comp]
  exact map_injective I hf

end

/--
Instance `flat_of_isNoetherian` / 实例 `flat_of_isNoetherian`

English:
instance flat_of_isNoetherian
  signature: : Module.Flat R (AdicCompletion I R)
  body: Module.Flat.iff_lTensor_injective'.mpr fun J =>
    tensor_map_id_left_injective_of_injective I (Submodule.injective_subtype J)

中文:
实例 flat_of_isNoetherian
  签名: : Module.Flat R (AdicCompletion I R)
  定义体: Module.Flat.iff_lTensor_injective'.mpr fun J =>
    tensor_map_id_left_injective_of_injective I (Submodule.injective_subtype J)

Depends on / 依赖: Module, Module.Flat.iff_lTensor_injective, Submodule, Submodule.injective_subtype, iff_lTensor_injective, injective_subtype, tensor_map_id_left_injective_of_injective
-/
instance flat_of_isNoetherian : Module.Flat R (AdicCompletion I R) :=
  Module.Flat.iff_lTensor_injective'.mpr fun J =>
    tensor_map_id_left_injective_of_injective I (Submodule.injective_subtype J)

end Noetherian

end AdicCompletion
