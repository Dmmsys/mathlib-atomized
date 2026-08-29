/-
Copyright (c) 2024 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
module

public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.LinearAlgebra.SModEq.Pointwise
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra

/-!
# Functoriality of adic completions

In this file we establish functorial properties of the adic completion.

## Main definitions

- `AdicCauchySequence.map I f`: the linear map on `I`-adic Cauchy sequences induced by `f`
- `AdicCompletion.map I f`: the linear map on `I`-adic completions induced by `f`

## Main results

- `sumEquivOfFintype`: adic completion commutes with finite sums
- `piEquivOfFintype`: adic completion commutes with finite products

-/

@[expose] public section

suppress_compilation

variable {R : Type*} [CommRing R] (I : Ideal R)
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {P : Type*} [AddCommGroup P] [Module R P]
variable {T : Type*} [AddCommGroup T] [Module (AdicCompletion I R) T]

namespace LinearMap

/--
Definition of `reduceModIdeal` / `reduceModIdeal` 的定义

English:
definition reduceModIdeal
  signature: (f : M ->ₗ[R] N)
  body: LinearMap.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
    Submodule.mapQ (I • ⊤ : Submodule R M) (I • ⊤ : Submodule R N) f
      (fun x hx => by
        refine Submodule.smul_induction_on hx (fun r hr x _ => ?_) (fun x y hx hy => ?_)
        · simp [Submodule.smul_mem_smul hr Submodule.me

中文:
定义 reduceModIdeal
  签名: (f : M ->ₗ[R] N)
  定义体: LinearMap.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
    Submodule.mapQ (I • ⊤ : Submodule R M) (I • ⊤ : Submodule R N) f
      (fun x hx => by
        refine Submodule.smul_induction_on hx (fun r hr x _ => ?_) (fun x y hx hy => ?_)
        · simp [Submodule.smul_mem_smul hr Submodule.me

Depends on / 依赖: Ideal.Quotient.mk_surjective, LinearMap, LinearMap.extendScalarsOfSurjective, Quotient, Submodule, Submodule.add_mem, Submodule.mapQ, Submodule.mem_top, Submodule.smul_induction_on, Submodule.smul_mem_smul, add_mem, extendScalarsOfSurjective, mem_top, mk_surjective, smul_induction_on, smul_mem_smul
-/
def reduceModIdeal (f : M ->ₗ[R] N) :
    M ⧸ (I • ⊤ : Submodule R M) ->ₗ[R ⧸ I] N ⧸ (I • ⊤ : Submodule R N) :=
LinearMap.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
    Submodule.mapQ (I • ⊤ : Submodule R M) (I • ⊤ : Submodule R N) f
      (fun x hx => by
        refine Submodule.smul_induction_on hx (fun r hr x _ => ?_) (fun x y hx hy => ?_)
        · simp [Submodule.smul_mem_smul hr Submodule.mem_top]
        · simp [Submodule.add_mem _ hx hy])

@[simp]
/--
theorem `reduceModIdeal_apply` / 定理 `reduceModIdeal_apply`

English:
theorem reduceModIdeal_apply
  given: (f : M ->ₗ[R] N) (x : M)
  proof: rfl

中文:
定理 reduceModIdeal_apply
  条件: (f : M ->ₗ[R] N) (x : M)
  证明: rfl

Depends on / 依赖: Submodule
-/
theorem reduceModIdeal_apply (f : M ->ₗ[R] N) (x : M) :
    (f.reduceModIdeal I) (Submodule.Quotient.mk (p := (I • ⊤ : Submodule R M)) x) =
      Submodule.Quotient.mk (p := (I • ⊤ : Submodule R N)) (f x) :=
  rfl

end LinearMap

namespace AdicCompletion

open LinearMap

set_option backward.isDefEq.respectTransparency false in
/--
theorem `transitionMap_comp_reduceModIdeal` / 定理 `transitionMap_comp_reduceModIdeal`

English:
theorem transitionMap_comp_reduceModIdeal
  statement: (f : M ->ₗ[R] N) {m n : Nat}
  proof: by
  ext x
  simp

中文:
定理 transitionMap_comp_reduceModIdeal
  结论: (f : M ->ₗ[R] N) {m n : 自然数}
  证明: by
  ext x
  simp
-/
theorem transitionMap_comp_reduceModIdeal (f : M ->ₗ[R] N) {m n : Nat}
    (hmn : m <= n) : transitionMap I N hmn ∘ₗ f.reduceModIdeal (I ^ n) =
      (f.reduceModIdeal (I ^ m) : _ ->ₗ[R] _) ∘ₗ transitionMap I M hmn := by
  ext x
  simp

namespace AdicCauchySequence

set_option backward.isDefEq.respectTransparency false in
/-- A linear map induces a linear map on adic Cauchy sequences. -/
@[simps]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : M ->ₗ[R] N)
  body: ⟨fun n => f (a n), fun {m n} hmn => by
    have hm : Submodule.map f (I ^ m • ⊤ : Submodule R M) <= (I ^ m • ⊤ : Submodule R N) := by
      rw [Submodule.map_smul'']
      exact smul_mono_right _ le_top
    apply SModEq.mono hm
    apply SModEq.map (a.property hmn) f⟩
  map_add' a b := by ext n; sim

中文:
定义 map
  签名: (f : M ->ₗ[R] N)
  定义体: ⟨fun n => f (a n), fun {m n} hmn => by
    have hm : Submodule.map f (I ^ m • ⊤ : Submodule R M) <= (I ^ m • ⊤ : Submodule R N) := by
      rw [Submodule.map_smul'']
      exact smul_mono_right _ le_top
    apply SModEq.mono hm
    apply SModEq.map (a.property hmn) f⟩
  map_add' a b := by ext n; sim

Depends on / 依赖: SModEq, SModEq.map, SModEq.mono, Submodule, Submodule.map, Submodule.map_smul, a.property, le_top, map_add, map_smul, property, smul_mono_right
-/
def map (f : M ->ₗ[R] N) : AdicCauchySequence I M ->ₗ[R] AdicCauchySequence I N where
  toFun a := ⟨fun n => f (a n), fun {m n} hmn => by
    have hm : Submodule.map f (I ^ m • ⊤ : Submodule R M) <= (I ^ m • ⊤ : Submodule R N) := by
      rw [Submodule.map_smul'']
      exact smul_mono_right _ le_top
    apply SModEq.mono hm
    apply SModEq.map (a.property hmn) f⟩
  map_add' a b := by ext n; simp
  map_smul' r a := by ext n; simp

variable (M) in
@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  statement: map I (LinearMap.id (M := M)) = LinearMap.id
  proof: rfl

中文:
定理 map_id
  结论: map I (LinearMap.id (M := M)) = LinearMap.id
  证明: rfl

Depends on / 依赖: LinearMap, LinearMap.id
-/
theorem map_id : map I (LinearMap.id (M := M)) = LinearMap.id :=
  rfl

/--
theorem `map_comp` / 定理 `map_comp`

English:
theorem map_comp
  given: (f : M ->ₗ[R] N) (g : N ->ₗ[R] P)
  proof: rfl

中文:
定理 map_comp
  条件: (f : M ->ₗ[R] N) (g : N ->ₗ[R] P)
  证明: rfl
-/
theorem map_comp (f : M ->ₗ[R] N) (g : N ->ₗ[R] P) :
    map I g ∘ₗ map I f = map I (g ∘ₗ f) :=
  rfl

/--
theorem `map_comp_apply` / 定理 `map_comp_apply`

English:
theorem map_comp_apply
  given: (f : M ->ₗ[R] N) (g : N ->ₗ[R] P) (a : AdicCauchySequence I M)
  proof: rfl

@[simp]

中文:
定理 map_comp_apply
  条件: (f : M ->ₗ[R] N) (g : N ->ₗ[R] P) (a : AdicCauchySequence I M)
  证明: rfl

@[simp]
-/
theorem map_comp_apply (f : M ->ₗ[R] N) (g : N ->ₗ[R] P) (a : AdicCauchySequence I M) :
    map I g (map I f a) = map I (g ∘ₗ f) a :=
  rfl

@[simp]
/--
theorem `map_zero` / 定理 `map_zero`

English:
theorem map_zero
  statement: map I (0 : M ->ₗ[R] N) = 0
  proof: rfl

中文:
定理 map_zero
  结论: map I (0 : M ->ₗ[R] N) = 0
  证明: rfl
-/
theorem map_zero : map I (0 : M ->ₗ[R] N) = 0 :=
  rfl

end AdicCauchySequence

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : M ->ₗ[R] N)
  body: AdicCompletion.lift I (fun n => reduceModIdeal (I ^ n) f ∘ₗ AdicCompletion.eval I M n)
    (fun {m n} hmn => by rw [← comp_assoc, AdicCompletion.transitionMap_comp_reduceModIdeal,
        comp_assoc, transitionMap_comp_eval])
  map_smul' r x := by
    ext
    dsimp
    rw [val_smul_eq_evalₐ_smul]; r

中文:
定义 map
  签名: (f : M ->ₗ[R] N)
  定义体: AdicCompletion.lift I (fun n => reduceModIdeal (I ^ n) f ∘ₗ AdicCompletion.eval I M n)
    (fun {m n} hmn => by rw [← comp_assoc, AdicCompletion.transitionMap_comp_reduceModIdeal,
        comp_assoc, transitionMap_comp_eval])
  map_smul' r x := by
    ext
    dsimp
    rw [val_smul_eq_evalₐ_smul]; r

Depends on / 依赖: AdicCompletion, AdicCompletion.eval, AdicCompletion.lift, reduceModIdeal
-/
def map (f : M ->ₗ[R] N) :
    AdicCompletion I M ->ₗ[AdicCompletion I R] AdicCompletion I N where
  __ := AdicCompletion.lift I (fun n => reduceModIdeal (I ^ n) f ∘ₗ AdicCompletion.eval I M n)
    (fun {m n} hmn => by rw [← comp_assoc, AdicCompletion.transitionMap_comp_reduceModIdeal,
        comp_assoc, transitionMap_comp_eval])
  map_smul' r x := by
    ext
    dsimp
    rw [val_smul_eq_evalₐ_smul]; rw [val_smul_eq_evalₐ_smul]; rw [map_smul]

@[simp]
/--
theorem `map_val_apply` / 定理 `map_val_apply`

English:
theorem map_val_apply
  given: (f : M ->ₗ[R] N) {n : Nat} (x : AdicCompletion I M)
  proof: rfl

中文:
定理 map_val_apply
  条件: (f : M ->ₗ[R] N) {n : 自然数} (x : AdicCompletion I M)
  证明: rfl
-/
theorem map_val_apply (f : M ->ₗ[R] N) {n : Nat} (x : AdicCompletion I M) :
    (map I f x).val n = f.reduceModIdeal (I ^ n) (x.val n) :=
  rfl

/--
theorem `map_ext` / 定理 `map_ext`

English:
theorem map_ext
  statement: {N} {f g : AdicCompletion I M -> N}
  proof: by
  ext x
  apply induction_on I M x h

中文:
定理 map_ext
  结论: {N} {f g : AdicCompletion I M -> N}
  证明: by
  ext x
  apply induction_on I M x h

Depends on / 依赖: induction_on
-/
theorem map_ext {N} {f g : AdicCompletion I M -> N}
    (h : forall (a : AdicCauchySequence I M),
      f (AdicCompletion.mk I M a) = g (AdicCompletion.mk I M a)) :
    f = g := by
  ext x
  apply induction_on I M x h

/-- Equality of linear maps out of an adic completion can be checked on Cauchy sequences. -/
@[ext]
/--
theorem `map_ext'` / 定理 `map_ext'`

English:
theorem map_ext'
  statement: {f g : AdicCompletion I M ->ₗ[AdicCompletion I R] T}
  proof: by
  ext x
  apply induction_on I M x h

中文:
定理 map_ext'
  结论: {f g : AdicCompletion I M ->ₗ[AdicCompletion I R] T}
  证明: by
  ext x
  apply induction_on I M x h

Depends on / 依赖: induction_on
-/
theorem map_ext' {f g : AdicCompletion I M ->ₗ[AdicCompletion I R] T}
    (h : forall (a : AdicCauchySequence I M),
      f (AdicCompletion.mk I M a) = g (AdicCompletion.mk I M a)) :
    f = g := by
  ext x
  apply induction_on I M x h

/-- Equality of linear maps out of an adic completion can be checked on Cauchy sequences. -/
@[ext]
/--
theorem `map_ext''` / 定理 `map_ext''`

English:
theorem map_ext''
  statement: {f g : AdicCompletion I M ->ₗ[R] N}
  proof: by
  ext x
  apply induction_on I M x (fun a => LinearMap.ext_iff.mp h a)

中文:
定理 map_ext''
  结论: {f g : AdicCompletion I M ->ₗ[R] N}
  证明: by
  ext x
  apply induction_on I M x (fun a => LinearMap.ext_iff.mp h a)

Depends on / 依赖: LinearMap, LinearMap.ext_iff.mp, ext_iff, induction_on
-/
theorem map_ext'' {f g : AdicCompletion I M ->ₗ[R] N}
    (h : f.comp (AdicCompletion.mk I M) = g.comp (AdicCompletion.mk I M)) :
    f = g := by
  ext x
  apply induction_on I M x (fun a => LinearMap.ext_iff.mp h a)

variable (M) in
@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  proof: by
  ext a n
  simp

中文:
定理 map_id
  证明: by
  ext a n
  simp
-/
theorem map_id :
    map I (LinearMap.id (M := M)) =
      LinearMap.id (R := AdicCompletion I R) (M := AdicCompletion I M) := by
  ext a n
  simp

/--
theorem `map_comp` / 定理 `map_comp`

English:
theorem map_comp
  given: (f : M ->ₗ[R] N) (g : N ->ₗ[R] P)
  proof: by
  ext
  simp

中文:
定理 map_comp
  条件: (f : M ->ₗ[R] N) (g : N ->ₗ[R] P)
  证明: by
  ext
  simp
-/
theorem map_comp (f : M ->ₗ[R] N) (g : N ->ₗ[R] P) :
    map I g ∘ₗ map I f = map I (g ∘ₗ f) := by
  ext
  simp

/--
theorem `map_comp_apply` / 定理 `map_comp_apply`

English:
theorem map_comp_apply
  given: (f : M ->ₗ[R] N) (g : N ->ₗ[R] P) (x : AdicCompletion I M)
  proof: by
  change (map I g ∘ₗ map I f) x = map I (g ∘ₗ f) x
  rw [map_comp]

@[simp]

中文:
定理 map_comp_apply
  条件: (f : M ->ₗ[R] N) (g : N ->ₗ[R] P) (x : AdicCompletion I M)
  证明: by
  change (map I g ∘ₗ map I f) x = map I (g ∘ₗ f) x
  rw [map_comp]

@[simp]

Depends on / 依赖: map_comp
-/
theorem map_comp_apply (f : M ->ₗ[R] N) (g : N ->ₗ[R] P) (x : AdicCompletion I M) :
    map I g (map I f x) = map I (g ∘ₗ f) x := by
  change (map I g ∘ₗ map I f) x = map I (g ∘ₗ f) x
  rw [map_comp]

@[simp]
/--
theorem `map_mk` / 定理 `map_mk`

English:
theorem map_mk
  given: (f : M ->ₗ[R] N) (a : AdicCauchySequence I M)
  proof: rfl

@[simp]

中文:
定理 map_mk
  条件: (f : M ->ₗ[R] N) (a : AdicCauchySequence I M)
  证明: rfl

@[simp]
-/
theorem map_mk (f : M ->ₗ[R] N) (a : AdicCauchySequence I M) :
    map I f (AdicCompletion.mk I M a) =
      AdicCompletion.mk I N (AdicCauchySequence.map I f a) :=
  rfl

@[simp]
/--
theorem `map_zero` / 定理 `map_zero`

English:
theorem map_zero
  statement: map I (0 : M ->ₗ[R] N) = 0
  proof: by
  ext
  simp

中文:
定理 map_zero
  结论: map I (0 : M ->ₗ[R] N) = 0
  证明: by
  ext
  simp
-/
theorem map_zero : map I (0 : M ->ₗ[R] N) = 0 := by
  ext
  simp

/--
theorem `map_of` / 定理 `map_of`

English:
theorem map_of
  given: (f : M ->ₗ[R] N) (x : M)
  statement: map I f (of I M x) = of I N (f x)
  proof: rfl

中文:
定理 map_of
  条件: (f : M ->ₗ[R] N) (x : M)
  结论: map I f (of I M x) = of I N (f x)
  证明: rfl
-/
theorem map_of (f : M ->ₗ[R] N) (x : M) : map I f (of I M x) = of I N (f x) :=
  rfl

/--
Definition of `congr` / `congr` 的定义

English:
definition congr
  signature: (f : M ≃ₗ[R] N)
  body: LinearEquiv.ofLinearMap (map I f)
    (map I f.symm) (by simp [map_comp]) (by simp [map_comp])

@[simp]

中文:
定义 congr
  签名: (f : M ≃ₗ[R] N)
  定义体: LinearEquiv.ofLinearMap (map I f)
    (map I f.symm) (by simp [map_comp]) (by simp [map_comp])

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.ofLinearMap, f.symm, map_comp, ofLinearMap
-/
def congr (f : M ≃ₗ[R] N) :
    AdicCompletion I M ≃ₗ[AdicCompletion I R] AdicCompletion I N :=
  LinearEquiv.ofLinearMap (map I f)
    (map I f.symm) (by simp [map_comp]) (by simp [map_comp])

@[simp]
/--
theorem `congr_apply` / 定理 `congr_apply`

English:
theorem congr_apply
  given: (f : M ≃ₗ[R] N) (x : AdicCompletion I M)
  proof: rfl

@[simp]

中文:
定理 congr_apply
  条件: (f : M ≃ₗ[R] N) (x : AdicCompletion I M)
  证明: rfl

@[simp]
-/
theorem congr_apply (f : M ≃ₗ[R] N) (x : AdicCompletion I M) :
    congr I f x = map I f x :=
  rfl

@[simp]
/--
theorem `congr_symm_apply` / 定理 `congr_symm_apply`

English:
theorem congr_symm_apply
  given: (f : M ≃ₗ[R] N) (x : AdicCompletion I N)
  proof: rfl

中文:
定理 congr_symm_apply
  条件: (f : M ≃ₗ[R] N) (x : AdicCompletion I N)
  证明: rfl
-/
theorem congr_symm_apply (f : M ≃ₗ[R] N) (x : AdicCompletion I N) :
    (congr I f).symm x = map I f.symm x :=
  rfl

section Families

/-! ### Adic completion in families

In this section we consider a family `M : ι → Type*` of `R`-modules. Purely from
the formal properties of adic completions we obtain two canonical maps

- `AdicCompletion I (∀ j, M j) →ₗ[R] ∀ j, AdicCompletion I (M j)`
- `(⨁ j, (AdicCompletion I (M j))) →ₗ[R] AdicCompletion I (⨁ j, M j)`

If `ι` is finite, both are isomorphisms and, modulo
the equivalence `⨁ j, (AdicCompletion I (M j)` and `∀ j, AdicCompletion I (M j)`,
inverse to each other.

-/

variable {ι : Type*} (M : ι -> Type*) [forall i, AddCommGroup (M i)]
  [forall i, Module R (M i)]

section Pi

/-- The canonical map from the adic completion of the product to the product of the
adic completions. -/
@[simps!]
/--
Definition of `pi` / `pi` 的定义

English:
definition pi
  signature: : AdicCompletion I (forall j, M j) ->ₗ[AdicCompletion I R] forall j, AdicCompletion I (M j)
  body: LinearMap.pi (fun j => map I (LinearMap.proj j))

中文:
定义 pi
  签名: : AdicCompletion I (对任意 j, M j) ->ₗ[AdicCompletion I R] 对任意 j, AdicCompletion I (M j)
  定义体: LinearMap.pi (fun j => map I (LinearMap.proj j))

Depends on / 依赖: LinearMap, LinearMap.pi, LinearMap.proj
-/
def pi : AdicCompletion I (forall j, M j) ->ₗ[AdicCompletion I R] forall j, AdicCompletion I (M j) :=
  LinearMap.pi (fun j => map I (LinearMap.proj j))

end Pi

section Sum

open DirectSum

/--
Definition of `sum` / `sum` 的定义

English:
definition sum
  signature: [DecidableEq ι]
  body: toModule (AdicCompletion I R) ι (AdicCompletion I (⨁ j, M j))
    (fun j => map I (lof R ι M j))

@[simp]

中文:
定义 sum
  签名: [DecidableEq ι]
  定义体: toModule (AdicCompletion I R) ι (AdicCompletion I (⨁ j, M j))
    (fun j => map I (lof R ι M j))

@[simp]

Depends on / 依赖: AdicCompletion, toModule
-/
def sum [DecidableEq ι] :
    (⨁ j, (AdicCompletion I (M j))) ->ₗ[AdicCompletion I R] AdicCompletion I (⨁ j, M j) :=
  toModule (AdicCompletion I R) ι (AdicCompletion I (⨁ j, M j))
    (fun j => map I (lof R ι M j))

@[simp]
/--
theorem `sum_lof` / 定理 `sum_lof`

English:
theorem sum_lof
  given: [DecidableEq ι] (j : ι) (x : AdicCompletion I (M j))
  proof: by
  simp [sum]

@[simp]

中文:
定理 sum_lof
  条件: [DecidableEq ι] (j : ι) (x : AdicCompletion I (M j))
  证明: by
  simp [sum]

@[simp]
-/
theorem sum_lof [DecidableEq ι] (j : ι) (x : AdicCompletion I (M j)) :
    sum I M ((DirectSum.lof (AdicCompletion I R) ι (fun i => AdicCompletion I (M i)) j) x) =
      map I (lof R ι M j) x := by
  simp [sum]

@[simp]
/--
theorem `sum_of` / 定理 `sum_of`

English:
theorem sum_of
  given: [DecidableEq ι] (j : ι) (x : AdicCompletion I (M j))
  proof: by
  rw [← lof_eq_of R]
  apply sum_lof

中文:
定理 sum_of
  条件: [DecidableEq ι] (j : ι) (x : AdicCompletion I (M j))
  证明: by
  rw [← lof_eq_of R]
  apply sum_lof

Depends on / 依赖: lof_eq_of, sum_lof
-/
theorem sum_of [DecidableEq ι] (j : ι) (x : AdicCompletion I (M j)) :
    sum I M ((DirectSum.of (fun i => AdicCompletion I (M i)) j) x) =
      map I (lof R ι M j) x := by
  rw [← lof_eq_of R]
  apply sum_lof

variable [Fintype ι]

/--
Definition of `sumInv` / `sumInv` 的定义

English:
definition sumInv
  signature: : AdicCompletion I (⨁ j, M j) ->ₗ[AdicCompletion I R] (⨁ j, (AdicCompletion I (M j)))
  body: letI f := map I (linearEquivFunOnFintype R ι M)
  letI g := linearEquivFunOnFintype (AdicCompletion I R) ι (fun j => AdicCompletion I (M j))
  g.symm.toLinearMap ∘ₗ pi I M ∘ₗ f

@[simp]

中文:
定义 sumInv
  签名: : AdicCompletion I (⨁ j, M j) ->ₗ[AdicCompletion I R] (⨁ j, (AdicCompletion I (M j)))
  定义体: letI f := map I (linearEquivFunOnFintype R ι M)
  letI g := linearEquivFunOnFintype (AdicCompletion I R) ι (fun j => AdicCompletion I (M j))
  g.symm.toLinearMap ∘ₗ pi I M ∘ₗ f

@[simp]

Depends on / 依赖: AdicCompletion, g.symm.toLinearMap, linearEquivFunOnFintype, toLinearMap
-/
def sumInv : AdicCompletion I (⨁ j, M j) ->ₗ[AdicCompletion I R] (⨁ j, (AdicCompletion I (M j))) :=
  letI f := map I (linearEquivFunOnFintype R ι M)
  letI g := linearEquivFunOnFintype (AdicCompletion I R) ι (fun j => AdicCompletion I (M j))
  g.symm.toLinearMap ∘ₗ pi I M ∘ₗ f

@[simp]
/--
theorem `component_sumInv` / 定理 `component_sumInv`

English:
theorem component_sumInv
  given: (x : AdicCompletion I (⨁ j, M j)) (j : ι)
  proof: by
  apply induction_on I _ x (fun x => ?_)
  rfl

@[simp]

中文:
定理 component_sumInv
  条件: (x : AdicCompletion I (⨁ j, M j)) (j : ι)
  证明: by
  apply induction_on I _ x (fun x => ?_)
  rfl

@[simp]

Depends on / 依赖: induction_on
-/
theorem component_sumInv (x : AdicCompletion I (⨁ j, M j)) (j : ι) :
    component (AdicCompletion I R) ι _ j (sumInv I M x) =
      map I (component R ι _ j) x := by
  apply induction_on I _ x (fun x => ?_)
  rfl

@[simp]
/--
theorem `sumInv_apply` / 定理 `sumInv_apply`

English:
theorem sumInv_apply
  given: (x : AdicCompletion I (⨁ j, M j)) (j : ι)
  proof: by
  apply induction_on I _ x (fun x => ?_)
  rfl

中文:
定理 sumInv_apply
  条件: (x : AdicCompletion I (⨁ j, M j)) (j : ι)
  证明: by
  apply induction_on I _ x (fun x => ?_)
  rfl

Depends on / 依赖: induction_on
-/
theorem sumInv_apply (x : AdicCompletion I (⨁ j, M j)) (j : ι) :
    (sumInv I M x) j = map I (component R ι _ j) x := by
  apply induction_on I _ x (fun x => ?_)
  rfl

variable [DecidableEq ι]

/--
theorem `sumInv_comp_sum` / 定理 `sumInv_comp_sum`

English:
theorem sumInv_comp_sum
  statement: sumInv I M ∘ₗ sum I M = LinearMap.id
  proof: by
  ext j x : 2
  apply DirectSum.ext_component (AdicCompletion I R) (fun i => ?_)
  ext n
  simp only [LinearMap.coe_comp, Function.comp_apply, sum_lof, map_mk, component_sumInv,
    mk_apply_coe, AdicCauchySequence.map_apply_coe, Submodule.mkQ_apply, LinearMap.id_comp]
  rw [DirectSum.component.o

中文:
定理 sumInv_comp_sum
  结论: sumInv I M ∘ₗ sum I M = LinearMap.id
  证明: by
  ext j x : 2
  apply DirectSum.ext_component (AdicCompletion I R) (fun i => ?_)
  ext n
  simp only [LinearMap.coe_comp, Function.comp_apply, sum_lof, map_mk, component_sumInv,
    mk_apply_coe, AdicCauchySequence.map_apply_coe, Submodule.mkQ_apply, LinearMap.id_comp]
  rw [DirectSum.component.o

Depends on / 依赖: AdicCauchySequence, AdicCauchySequence.map_apply_coe, AdicCompletion, DirectSum, DirectSum.component.of, DirectSum.ext_component, Function, Function.comp_apply, LinearMap, LinearMap.coe_comp, LinearMap.id_comp, Submodule, Submodule.mkQ_apply, coe_comp, comp_apply, component, component_sumInv, ext_component, id_comp, map_apply_coe
-/
theorem sumInv_comp_sum : sumInv I M ∘ₗ sum I M = LinearMap.id := by
  ext j x : 2
  apply DirectSum.ext_component (AdicCompletion I R) (fun i => ?_)
  ext n
  simp only [LinearMap.coe_comp, Function.comp_apply, sum_lof, map_mk, component_sumInv,
    mk_apply_coe, AdicCauchySequence.map_apply_coe, Submodule.mkQ_apply, LinearMap.id_comp]
  rw [DirectSum.component.of]; rw [DirectSum.component.of]
  split
  · next h => subst h; simp
  · simp

/--
theorem `sum_comp_sumInv` / 定理 `sum_comp_sumInv`

English:
theorem sum_comp_sumInv
  statement: sum I M ∘ₗ sumInv I M = LinearMap.id
  proof: by
  ext f n
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq, mk_apply_coe,
    Submodule.mkQ_apply]
  rw [← DirectSum.sum_univ_of (((sumInv I M) ((AdicCompletion.mk I (⨁ (j : ι)]; rw [M j)) f)))]
  simp only [sumInv_apply, map_mk, map_sum, sum_of, val_sum_apply, mk_app

中文:
定理 sum_comp_sumInv
  结论: sum I M ∘ₗ sumInv I M = LinearMap.id
  证明: by
  ext f n
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq, mk_apply_coe,
    Submodule.mkQ_apply]
  rw [← DirectSum.sum_univ_of (((sumInv I M) ((AdicCompletion.mk I (⨁ (j : ι)]; rw [M j)) f)))]
  simp only [sumInv_apply, map_mk, map_sum, sum_of, val_sum_apply, mk_app

Depends on / 依赖: AdicCauchySequence, AdicCauchySequence.map_apply_coe, AdicCompletion, AdicCompletion.mk, DirectSum, DirectSum.sum_univ_of, Function, Function.comp_apply, LinearMap, LinearMap.coe_comp, LinearMap.id_coe, Submodule, Submodule.mkQ_apply, apply_eq_component, coe_comp, comp_apply, id_coe, id_eq, lof_eq_of, map_apply_coe
-/
theorem sum_comp_sumInv : sum I M ∘ₗ sumInv I M = LinearMap.id := by
  ext f n
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq, mk_apply_coe,
    Submodule.mkQ_apply]
  rw [← DirectSum.sum_univ_of (((sumInv I M) ((AdicCompletion.mk I (⨁ (j : ι)]; rw [M j)) f)))]
  simp only [sumInv_apply, map_mk, map_sum, sum_of, val_sum_apply, mk_apply_coe,
    AdicCauchySequence.map_apply_coe]
  simp only [← Submodule.mkQ_apply, ← map_sum, ← apply_eq_component, lof_eq_of,
    DirectSum.sum_univ_of]

/--
Definition of `sumEquivOfFintype` / `sumEquivOfFintype` 的定义

English:
definition sumEquivOfFintype
  signature: :
  body: LinearEquiv.ofLinearMap (sum I M) (sumInv I M) (sum_comp_sumInv I M) (sumInv_comp_sum I M)

@[simp]

中文:
定义 sumEquivOfFintype
  签名: :
  定义体: LinearEquiv.ofLinearMap (sum I M) (sumInv I M) (sum_comp_sumInv I M) (sumInv_comp_sum I M)

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.ofLinearMap, ofLinearMap, sumInv, sumInv_comp_sum, sum_comp_sumInv
-/
def sumEquivOfFintype :
    (⨁ j, (AdicCompletion I (M j))) ≃ₗ[AdicCompletion I R] AdicCompletion I (⨁ j, M j) :=
  LinearEquiv.ofLinearMap (sum I M) (sumInv I M) (sum_comp_sumInv I M) (sumInv_comp_sum I M)

@[simp]
/--
theorem `sumEquivOfFintype_apply` / 定理 `sumEquivOfFintype_apply`

English:
theorem sumEquivOfFintype_apply
  given: (x : ⨁ j, (AdicCompletion I (M j)))
  proof: rfl

@[simp]

中文:
定理 sumEquivOfFintype_apply
  条件: (x : ⨁ j, (AdicCompletion I (M j)))
  证明: rfl

@[simp]
-/
theorem sumEquivOfFintype_apply (x : ⨁ j, (AdicCompletion I (M j))) :
    sumEquivOfFintype I M x = sum I M x :=
  rfl

@[simp]
/--
theorem `sumEquivOfFintype_symm_apply` / 定理 `sumEquivOfFintype_symm_apply`

English:
theorem sumEquivOfFintype_symm_apply
  given: (x : AdicCompletion I (⨁ j, M j))
  proof: rfl

中文:
定理 sumEquivOfFintype_symm_apply
  条件: (x : AdicCompletion I (⨁ j, M j))
  证明: rfl
-/
theorem sumEquivOfFintype_symm_apply (x : AdicCompletion I (⨁ j, M j)) :
    (sumEquivOfFintype I M).symm x = sumInv I M x :=
  rfl

end Sum

section Pi

open DirectSum

variable [DecidableEq ι] [Fintype ι]

/--
Definition of `piEquivOfFintype` / `piEquivOfFintype` 的定义

English:
definition piEquivOfFintype
  signature: :
  body: letI f := (congr I (linearEquivFunOnFintype R ι M)).symm
  letI g := (linearEquivFunOnFintype (AdicCompletion I R) ι (fun j => AdicCompletion I (M j)))
  f.trans ((sumEquivOfFintype I M).symm.trans g)

@[simp]

中文:
定义 piEquivOfFintype
  签名: :
  定义体: letI f := (congr I (linearEquivFunOnFintype R ι M)).symm
  letI g := (linearEquivFunOnFintype (AdicCompletion I R) ι (fun j => AdicCompletion I (M j)))
  f.trans ((sumEquivOfFintype I M).symm.trans g)

@[simp]

Depends on / 依赖: AdicCompletion, f.trans, linearEquivFunOnFintype, sumEquivOfFintype, symm.trans
-/
def piEquivOfFintype :
    AdicCompletion I (forall j, M j) ≃ₗ[AdicCompletion I R] forall j, AdicCompletion I (M j) :=
  letI f := (congr I (linearEquivFunOnFintype R ι M)).symm
  letI g := (linearEquivFunOnFintype (AdicCompletion I R) ι (fun j => AdicCompletion I (M j)))
  f.trans ((sumEquivOfFintype I M).symm.trans g)

@[simp]
/--
theorem `piEquivOfFintype_apply` / 定理 `piEquivOfFintype_apply`

English:
theorem piEquivOfFintype_apply
  given: (x : AdicCompletion I (forall j, M j))
  proof: by
  simp [piEquivOfFintype, sumInv, map_comp_apply]

中文:
定理 piEquivOfFintype_apply
  条件: (x : AdicCompletion I (对任意 j, M j))
  证明: by
  simp [piEquivOfFintype, sumInv, map_comp_apply]

Depends on / 依赖: map_comp_apply, piEquivOfFintype, sumInv
-/
theorem piEquivOfFintype_apply (x : AdicCompletion I (forall j, M j)) :
    piEquivOfFintype I M x = pi I M x := by
  simp [piEquivOfFintype, sumInv, map_comp_apply]

/--
Definition of `piEquivFin` / `piEquivFin` 的定义

English:
definition piEquivFin
  signature: (n : Nat)
  body: piEquivOfFintype I (ι := Fin n) (fun _ : Fin n => R)

中文:
定义 piEquivFin
  签名: (n : 自然数)
  定义体: piEquivOfFintype I (ι := Fin n) (fun _ : Fin n => R)

Depends on / 依赖: piEquivOfFintype
-/
def piEquivFin (n : Nat) :
    AdicCompletion I (Fin n -> R) ≃ₗ[AdicCompletion I R] Fin n -> AdicCompletion I R :=
  piEquivOfFintype I (ι := Fin n) (fun _ : Fin n => R)

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
@[simp]
/--
theorem `piEquivFin_apply` / 定理 `piEquivFin_apply`

English:
theorem piEquivFin_apply
  given: (n : Nat) (x : AdicCompletion I (Fin n -> R))
  proof: by
  simp only [piEquivFin, piEquivOfFintype_apply]

中文:
定理 piEquivFin_apply
  条件: (n : 自然数) (x : AdicCompletion I (Fin n -> R))
  证明: by
  simp only [piEquivFin, piEquivOfFintype_apply]

Depends on / 依赖: piEquivFin, piEquivOfFintype_apply
-/
theorem piEquivFin_apply (n : Nat) (x : AdicCompletion I (Fin n -> R)) :
    piEquivFin I n x = pi I (fun _ : Fin n => R) x := by
  simp only [piEquivFin, piEquivOfFintype_apply]

end Pi

end Families

open Submodule

variable {I}

set_option backward.isDefEq.respectTransparency false in
/--
theorem `exists_smodEq_pow_add_one_smul` / 定理 `exists_smodEq_pow_add_one_smul`

English:
theorem exists_smodEq_pow_add_one_smul
  statement: {f : M ->ₗ[R] N}
  proof: by
  induction hy using smul_induction_on' with
  | smul r hr y _ =>
    obtain ⟨x, hx⟩ := h (mkQ _ y)
    use r • x, smul_mem_smul hr mem_top
    simp only [coe_comp, Function.comp_apply, mkQ_apply, ← SModEq.def, map_smul] at ⊢ hx
    rw [pow_succ]; rw [← smul_smul]
    exact SModEq.smul' hx hr
  |

中文:
定理 exists_smodEq_pow_add_one_smul
  结论: {f : M ->ₗ[R] N}
  证明: by
  induction hy using smul_induction_on' with
  | smul r hr y _ =>
    obtain ⟨x, hx⟩ := h (mkQ _ y)
    use r • x, smul_mem_smul hr mem_top
    simp only [coe_comp, Function.comp_apply, mkQ_apply, ← SModEq.def, map_smul] at ⊢ hx
    rw [pow_succ]; rw [← smul_smul]
    exact SModEq.smul' hx hr
  |

Depends on / 依赖: Function, Function.comp_apply, SModEq, SModEq.add, SModEq.def, SModEq.smul, add_mem, coe_comp, comp_apply, map_add, map_smul, mem_top, mkQ_apply, pow_succ, smul_induction_on, smul_mem_smul, smul_smul
-/
theorem exists_smodEq_pow_add_one_smul {f : M ->ₗ[R] N}
    (h : Function.Surjective (mkQ (I • ⊤) ∘ₗ f)) {y : N} {n : Nat}
    (hy : y in (I ^ n • ⊤ : Submodule R N)) :
    exists x in (I ^ n • ⊤ : Submodule R M), f x ≡ y [SMOD (I ^ (n + 1) • ⊤ : Submodule R N)] := by
  induction hy using smul_induction_on' with
  | smul r hr y _ =>
    obtain ⟨x, hx⟩ := h (mkQ _ y)
    use r • x, smul_mem_smul hr mem_top
    simp only [coe_comp, Function.comp_apply, mkQ_apply, ← SModEq.def, map_smul] at ⊢ hx
    rw [pow_succ]; rw [← smul_smul]
    exact SModEq.smul' hx hr
  | add y1 hy1 y2 hy2 ih1 ih2 =>
    obtain ⟨x1, hx1, hx1'⟩ := ih1
    obtain ⟨x2, hx2, hx2'⟩ := ih2
    use x1 + x2, add_mem hx1 hx2
    simp only [map_add]
    exact SModEq.add hx1' hx2'

/--
theorem `exists_smodEq_pow_smul_top_and_smodEq_pow_add_one_smul_top` / 定理 `exists_smodEq_pow_smul_top_and_smodEq_pow_add_one_smul_top`

English:
theorem exists_smodEq_pow_smul_top_and_smodEq_pow_add_one_smul_top
  statement: {f : M ->ₗ[R] N}
  proof: by
  obtain ⟨z, hz, hz'⟩ :=
    exists_smodEq_pow_add_one_smul h (y := y - f x) (SModEq.sub_mem.mp hxy.symm)
  use x + z
  constructor
  · simpa [SModEq.sub_mem]
  · simpa [SModEq.sub_mem, sub_sub_eq_add_sub, add_comm] using hz'

中文:
定理 exists_smodEq_pow_smul_top_and_smodEq_pow_add_one_smul_top
  结论: {f : M ->ₗ[R] N}
  证明: by
  obtain ⟨z, hz, hz'⟩ :=
    exists_smodEq_pow_add_one_smul h (y := y - f x) (SModEq.sub_mem.mp hxy.symm)
  use x + z
  constructor
  · simpa [SModEq.sub_mem]
  · simpa [SModEq.sub_mem, sub_sub_eq_add_sub, add_comm] using hz'

Depends on / 依赖: SModEq, SModEq.sub_mem, SModEq.sub_mem.mp, add_comm, exists_smodEq_pow_add_one_smul, hxy.symm, sub_mem, sub_sub_eq_add_sub
-/
theorem exists_smodEq_pow_smul_top_and_smodEq_pow_add_one_smul_top {f : M ->ₗ[R] N}
    (h : Function.Surjective (mkQ (I • ⊤) ∘ₗ f)) {x : M} {y : N} {n : Nat}
    (hxy : f x ≡ y [SMOD (I ^ n • ⊤ : Submodule R N)]) :
    exists x' : M, x ≡ x' [SMOD (I ^ n • ⊤ : Submodule R M)] ∧
    f x' ≡ y [SMOD (I ^ (n + 1) • ⊤ : Submodule R N)] := by
  obtain ⟨z, hz, hz'⟩ :=
    exists_smodEq_pow_add_one_smul h (y := y - f x) (SModEq.sub_mem.mp hxy.symm)
  use x + z
  constructor
  · simpa [SModEq.sub_mem]
  · simpa [SModEq.sub_mem, sub_sub_eq_add_sub, add_comm] using hz'

/--
theorem `exists_smodEq_pow_smul_top_and_mkQ_eq` / 定理 `exists_smodEq_pow_smul_top_and_mkQ_eq`

English:
theorem exists_smodEq_pow_smul_top_and_mkQ_eq
  statement: {f : M ->ₗ[R] N}
  proof: by
  obtain ⟨y0, hy0⟩ := mkQ_surjective _ y'
  have : f x ≡ y0 [SMOD (I ^ n • ⊤ : Submodule R N)] := by
    rw [SModEq]; rw [← mkQ_apply]; rw [← mkQ_apply]; rw [← factor_mk (pow_smul_top_le I N n.le_succ) y0]; rw [hy0]; rw [hyy']; rw [hxy]
  obtain ⟨x', hxx', hx'y0⟩ :=
    exists_smodEq_pow_smul_top

中文:
定理 exists_smodEq_pow_smul_top_and_mkQ_eq
  结论: {f : M ->ₗ[R] N}
  证明: by
  obtain ⟨y0, hy0⟩ := mkQ_surjective _ y'
  have : f x ≡ y0 [SMOD (I ^ n • ⊤ : Submodule R N)] := by
    rw [SModEq]; rw [← mkQ_apply]; rw [← mkQ_apply]; rw [← factor_mk (pow_smul_top_le I N n.le_succ) y0]; rw [hy0]; rw [hyy']; rw [hxy]
  obtain ⟨x', hxx', hx'y0⟩ :=
    exists_smodEq_pow_smul_top

Depends on / 依赖: SModEq, Submodule, exists_smodEq_pow_smul_top_and_smodEq_pow_add_one_smul_top, factor_mk, le_succ, mkQ_apply, mkQ_surjective, n.le_succ, pow_smul_top_le
-/
theorem exists_smodEq_pow_smul_top_and_mkQ_eq {f : M ->ₗ[R] N}
    (h : Function.Surjective (mkQ (I • ⊤) ∘ₗ f)) {x : M} {n : Nat}
    {y : N ⧸ (I ^ n • ⊤ : Submodule R N)} {y' : N ⧸ (I ^ (n + 1) • ⊤ : Submodule R N)}
    (hyy' : factor (pow_smul_top_le I N n.le_succ) y' = y) (hxy : mkQ _ (f x) = y) :
    exists x' : M, x ≡ x' [SMOD (I ^ n • ⊤ : Submodule R M)] ∧ mkQ _ (f x') = y' := by
  obtain ⟨y0, hy0⟩ := mkQ_surjective _ y'
  have : f x ≡ y0 [SMOD (I ^ n • ⊤ : Submodule R N)] := by
    rw [SModEq]; rw [← mkQ_apply]; rw [← mkQ_apply]; rw [← factor_mk (pow_smul_top_le I N n.le_succ) y0]; rw [hy0]; rw [hyy']; rw [hxy]
  obtain ⟨x', hxx', hx'y0⟩ :=
    exists_smodEq_pow_smul_top_and_smodEq_pow_add_one_smul_top h this
  use x', hxx'
  rwa [mkQ_apply, hx'y0]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `map_surjective_of_mkQ_comp_surjective` / 定理 `map_surjective_of_mkQ_comp_surjective`

English:
theorem map_surjective_of_mkQ_comp_surjective
  statement: {f : M ->ₗ[R] N}
  proof: by
  intro y
  suffices h : exists x : Nat -> M, forall n, x n ≡ x (n + 1) [SMOD (I ^ n • ⊤ : Submodule R M)] ∧
      Submodule.Quotient.mk (f (x n)) = eval I _ n y by
    obtain ⟨x, hx⟩ := h
    use AdicCompletion.mk I M ⟨x, fun h =>
        eq_factor_of_eq_factor_succ (fun _ _ => pow_smul_top_le I

中文:
定理 map_surjective_of_mkQ_comp_surjective
  结论: {f : M ->ₗ[R] N}
  证明: by
  intro y
  suffices h : exists x : Nat -> M, forall n, x n ≡ x (n + 1) [SMOD (I ^ n • ⊤ : Submodule R M)] ∧
      Submodule.Quotient.mk (f (x n)) = eval I _ n y by
    obtain ⟨x, hx⟩ := h
    use AdicCompletion.mk I M ⟨x, fun h =>
        eq_factor_of_eq_factor_succ (fun _ _ => pow_smul_top_le I

Depends on / 依赖: AdicCompletion, AdicCompletion.mk, Quotient, Submodule, Submodule.Quotient.equiv, Submodule.Quotient.mk, apply_fun, eq_factor_of_eq_factor_succ, pow_smul_top_le
-/
theorem map_surjective_of_mkQ_comp_surjective {f : M ->ₗ[R] N}
    (h : Function.Surjective (mkQ (I • ⊤) ∘ₗ f)) : Function.Surjective (map I f) := by
  intro y
  suffices h : exists x : Nat -> M, forall n, x n ≡ x (n + 1) [SMOD (I ^ n • ⊤ : Submodule R M)] ∧
      Submodule.Quotient.mk (f (x n)) = eval I _ n y by
    obtain ⟨x, hx⟩ := h
    use AdicCompletion.mk I M ⟨x, fun h =>
        eq_factor_of_eq_factor_succ (fun _ _ => pow_smul_top_le I M) _ (fun n => (hx n).1) h⟩
    ext n
    simp [hx n]
  let x : (n : Nat) -> {m : M // Submodule.Quotient.mk (f m) = eval I _ n y} := fun n => by
    induction n with
    | zero =>
      use 0
      apply_fun (Submodule.Quotient.equiv (I ^ 0 • ⊤) ⊤ (.refl R N) (by simp)).toEquiv
      exact Subsingleton.elim _ _
    | succ n xn =>
      choose z hz using exists_smodEq_pow_smul_top_and_mkQ_eq h
          (y' := eval _ _ (n + 1) y) (by simp) xn.2
      exact ⟨z, hz.2⟩
  exact ⟨fun n => (x n).val, fun n => ⟨(Classical.choose_spec (exists_smodEq_pow_smul_top_and_mkQ_eq
      h (y' := eval I _ (n + 1) y) (by simp) (x n).2)).1, (x n).property⟩⟩

end AdicCompletion

open AdicCompletion Submodule

variable {I}

/--
theorem `surjective_of_mkQ_comp_surjective` / 定理 `surjective_of_mkQ_comp_surjective`

English:
theorem surjective_of_mkQ_comp_surjective
  statement: [IsPrecomplete I M] [IsHausdorff I N]
  proof: by
  intro y
  obtain ⟨x', hx'⟩ := AdicCompletion.map_surjective_of_mkQ_comp_surjective h (of I N y)
  obtain ⟨x, hx⟩ := of_surjective I M x'
  use x
  rwa [← of_inj (I := I), ← map_of, hx]

中文:
定理 surjective_of_mkQ_comp_surjective
  结论: [IsPrecomplete I M] [IsHausdorff I N]
  证明: by
  intro y
  obtain ⟨x', hx'⟩ := AdicCompletion.map_surjective_of_mkQ_comp_surjective h (of I N y)
  obtain ⟨x, hx⟩ := of_surjective I M x'
  use x
  rwa [← of_inj (I := I), ← map_of, hx]

Depends on / 依赖: AdicCompletion, AdicCompletion.map_surjective_of_mkQ_comp_surjective, map_of, map_surjective_of_mkQ_comp_surjective, of_inj, of_surjective
-/
theorem surjective_of_mkQ_comp_surjective [IsPrecomplete I M] [IsHausdorff I N]
    {f : M ->ₗ[R] N} (h : Function.Surjective (mkQ (I • ⊤) ∘ₗ f)) : Function.Surjective f := by
  intro y
  obtain ⟨x', hx'⟩ := AdicCompletion.map_surjective_of_mkQ_comp_surjective h (of I N y)
  obtain ⟨x, hx⟩ := of_surjective I M x'
  use x
  rwa [← of_inj (I := I), ← map_of, hx]

variable {S : Type*} [CommRing S] (f : R ->+* S)

/--
theorem `surjective_of_mk_map_comp_surjective` / 定理 `surjective_of_mk_map_comp_surjective`

English:
theorem surjective_of_mk_map_comp_surjective
  statement: [IsPrecomplete I R] [haus : IsHausdorff (I.map f) S]
  proof: by
  let _ := f.toAlgebra
  let fₗ := (Algebra.ofId R S).toLinearMap
  change Function.Surjective ((restrictScalars R (I.map f)).mkQ ∘ₗ fₗ) at h
  have : I • ⊤ = restrictScalars R (Ideal.map f I) := by
    simp only [Ideal.smul_top_eq_map, restrictScalars_inj]
    rfl
  have _ := IsHausdorff.map_alg

中文:
定理 surjective_of_mk_map_comp_surjective
  结论: [IsPrecomplete I R] [haus : IsHausdorff (I.map f) S]
  证明: by
  let _ := f.toAlgebra
  let fₗ := (Algebra.ofId R S).toLinearMap
  change Function.Surjective ((restrictScalars R (I.map f)).mkQ ∘ₗ fₗ) at h
  have : I • ⊤ = restrictScalars R (Ideal.map f I) := by
    simp only [Ideal.smul_top_eq_map, restrictScalars_inj]
    rfl
  have _ := IsHausdorff.map_alg

Depends on / 依赖: Algebra, Algebra.ofId, Function, Function.Surjective, I.map, Ideal.map, Ideal.smul_top_eq_map, IsHausdorff, IsHausdorff.map_algebraMap_iff.mp, Surjective, f.toAlgebra, map_algebraMap_iff, restrictScalars, restrictScalars_inj, smul_top_eq_map, surjective_of_mkQ_comp_surjective, toAlgebra, toLinearMap
-/
theorem surjective_of_mk_map_comp_surjective [IsPrecomplete I R] [haus : IsHausdorff (I.map f) S]
    (h : Function.Surjective ((Ideal.Quotient.mk (I.map f)).comp f)) :
    Function.Surjective f := by
  let _ := f.toAlgebra
  let fₗ := (Algebra.ofId R S).toLinearMap
  change Function.Surjective ((restrictScalars R (I.map f)).mkQ ∘ₗ fₗ) at h
  have : I • ⊤ = restrictScalars R (Ideal.map f I) := by
    simp only [Ideal.smul_top_eq_map, restrictScalars_inj]
    rfl
  have _ := IsHausdorff.map_algebraMap_iff.mp haus
  apply surjective_of_mkQ_comp_surjective (I := I) (f := fₗ)
  rwa [Ideal.smul_top_eq_map]
