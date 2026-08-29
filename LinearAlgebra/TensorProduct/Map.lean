/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Tensor products and linear maps

This file defines `TensorProduct.map`, the `R`-linear map from `M ⊗ N` to `M₂ ⊗ N₂` defined by
a pair of linear (or more generally semilinear) maps `f : M → M₂` and `g : N → N₂`.

The notation `f ⊗ₘ g` is available for this map.

We also define one-sided versions `lTensor` and `rTensor`.

## Tags

bilinear, tensor, tensor product
-/

@[expose] public section

section Semiring

variable {R R₂ R₃ R' R'' : Type*}
variable [CommSemiring R] [CommSemiring R₂] [CommSemiring R₃] [Monoid R'] [Semiring R'']
variable {σ₁₂ : R ->+* R₂} {σ₂₃ : R₂ ->+* R₃} {σ₁₃ : R ->+* R₃}
variable {A M N P Q S : Type*}
variable {M₂ M₃ N₂ N₃ P' P₂ P₃ Q' Q₂ Q₃ : Type*}
variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [AddCommMonoid Q] [AddCommMonoid S]
variable [AddCommMonoid P'] [AddCommMonoid Q']
variable [AddCommMonoid M₂] [AddCommMonoid N₂] [AddCommMonoid P₂] [AddCommMonoid Q₂]
variable [AddCommMonoid M₃] [AddCommMonoid N₃] [AddCommMonoid P₃] [AddCommMonoid Q₃]
variable [DistribMulAction R' M]
variable [Module R'' M]
variable [Module R M] [Module R N] [Module R S]
variable [Module R P'] [Module R Q']
variable [Module R₂ M₂] [Module R₂ N₂] [Module R₂ P₂] [Module R₂ Q₂]
variable [Module R₃ M₃] [Module R₃ N₃] [Module R₃ P₃] [Module R₃ Q₃]

variable (M N)

namespace TensorProduct

variable [Module R P] [Module R Q]

variable {M N}

open LinearMap

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : M ->ₛₗ[σ₁₂] M₂) (g : N ->ₛₗ[σ₁₂] N₂)
  body: lift comp (compl₂ (mk _ _ _) g) f

@[inherit_doc] scoped[RingTheory.LinearMap] infix:70 " otimesₘ " => TensorProduct.map

@[simp]

中文:
定义 map
  签名: (f : M ->ₛₗ[σ₁₂] M₂) (g : N ->ₛₗ[σ₁₂] N₂)
  定义体: lift comp (compl₂ (mk _ _ _) g) f

@[inherit_doc] scoped[RingTheory.LinearMap] infix:70 " otimesₘ " => TensorProduct.map

@[simp]
-/
def map (f : M ->ₛₗ[σ₁₂] M₂) (g : N ->ₛₗ[σ₁₂] N₂) : M otimes[R] N ->ₛₗ[σ₁₂] M₂ otimes[R₂] N₂ :=
lift comp (compl₂ (mk _ _ _) g) f

@[inherit_doc] scoped[RingTheory.LinearMap] infix:70 " otimesₘ " => TensorProduct.map

@[simp]
/--
theorem `map_tmul` / 定理 `map_tmul`

English:
theorem map_tmul
  given: (f : M ->ₛₗ[σ₁₂] M₂) (g : N ->ₛₗ[σ₁₂] N₂) (m : M) (n : N)
  proof: rfl

中文:
定理 map_tmul
  条件: (f : M ->ₛₗ[σ₁₂] M₂) (g : N ->ₛₗ[σ₁₂] N₂) (m : M) (n : N)
  证明: rfl
-/
theorem map_tmul (f : M ->ₛₗ[σ₁₂] M₂) (g : N ->ₛₗ[σ₁₂] N₂) (m : M) (n : N) :
    map f g (m otimesₜ n) = f m otimesₜ g n :=
  rfl

/--
lemma `map_comp_comm_eq` / 引理 `map_comp_comm_eq`

English:
lemma map_comp_comm_eq
  given: (f : M ->ₛₗ[σ₁₂] M₂) (g : N ->ₛₗ[σ₁₂] N₂)
  proof: ext rfl

中文:
引理 map_comp_comm_eq
  条件: (f : M ->ₛₗ[σ₁₂] M₂) (g : N ->ₛₗ[σ₁₂] N₂)
  证明: ext rfl
-/
lemma map_comp_comm_eq (f : M ->ₛₗ[σ₁₂] M₂) (g : N ->ₛₗ[σ₁₂] N₂) :
    map f g ∘ₛₗ (TensorProduct.comm R N M).toLinearMap =
      (TensorProduct.comm R₂ N₂ M₂).toLinearMap ∘ₛₗ map g f :=
  ext rfl

/--
lemma `map_comm` / 引理 `map_comm`

English:
lemma map_comm
  given: (f : M ->ₛₗ[σ₁₂] M₂) (g : N ->ₛₗ[σ₁₂] N₂) (x : N otimes[R] M)
  proof: DFunLike.congr_fun (map_comp_comm_eq _ _) _

中文:
引理 map_comm
  条件: (f : M ->ₛₗ[σ₁₂] M₂) (g : N ->ₛₗ[σ₁₂] N₂) (x : N otimes[R] M)
  证明: DFunLike.congr_fun (map_comp_comm_eq _ _) _

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun, map_comp_comm_eq
-/
lemma map_comm (f : M ->ₛₗ[σ₁₂] M₂) (g : N ->ₛₗ[σ₁₂] N₂) (x : N otimes[R] M) :
    map f g (TensorProduct.comm R N M x) = TensorProduct.comm R₂ N₂ M₂ (map g f x) :=
  DFunLike.congr_fun (map_comp_comm_eq _ _) _

/--
theorem `range_map` / 定理 `range_map`

English:
theorem range_map
  given: (f : M ->ₗ[R] P) (g : N ->ₗ[R] Q)
  proof: by
  simp_rw [← Submodule.map_top, Submodule.map₂_map_map, ← map₂_mk_top_top_eq_top,
    Submodule.map_map₂]
  rfl

中文:
定理 range_map
  条件: (f : M ->ₗ[R] P) (g : N ->ₗ[R] Q)
  证明: by
  simp_rw [← Submodule.map_top, Submodule.map₂_map_map, ← map₂_mk_top_top_eq_top,
    Submodule.map_map₂]
  rfl

Depends on / 依赖: Submodule, Submodule.map, Submodule.map_map, Submodule.map_top, map_top, simp_rw
-/
theorem range_map (f : M ->ₗ[R] P) (g : N ->ₗ[R] Q) :
    range (map f g) = .map₂ (mk R _ _) (range f) (range g) := by
  simp_rw [← Submodule.map_top, Submodule.map₂_map_map, ← map₂_mk_top_top_eq_top,
    Submodule.map_map₂]
  rfl

/--
theorem `range_map_eq_span_tmul` / 定理 `range_map_eq_span_tmul`

English:
theorem range_map_eq_span_tmul
  given: (f : M ->ₗ[R] P) (g : N ->ₗ[R] Q)
  proof: by
  simp only [← Submodule.map_top, ← span_tmul_eq_top, Submodule.map_span]
  congr; ext t
  simp

中文:
定理 range_map_eq_span_tmul
  条件: (f : M ->ₗ[R] P) (g : N ->ₗ[R] Q)
  证明: by
  simp only [← Submodule.map_top, ← span_tmul_eq_top, Submodule.map_span]
  congr; ext t
  simp

Depends on / 依赖: Submodule, Submodule.map_span, Submodule.map_top, map_span, map_top, span_tmul_eq_top
-/
theorem range_map_eq_span_tmul (f : M ->ₗ[R] P) (g : N ->ₗ[R] Q) :
    range (map f g) = Submodule.span R { t | exists m n, f m otimesₜ g n = t } := by
  simp only [← Submodule.map_top, ← span_tmul_eq_top, Submodule.map_span]
  congr; ext t
  simp

/--
Definition of `mapIncl` / `mapIncl` 的定义

English:
abbreviation mapIncl
  signature: (p : Submodule R P) (q : Submodule R Q)
  body: map p.subtype q.subtype

中文:
缩写 mapIncl
  签名: (p : 子模 R P) (q : 子模 R Q)
  定义体: map p.subtype q.subtype

Depends on / 依赖: p.subtype, q.subtype, subtype
-/
abbrev mapIncl (p : Submodule R P) (q : Submodule R Q) : p otimes[R] q ->ₗ[R] P otimes[R] Q :=
  map p.subtype q.subtype

/--
lemma `range_mapIncl` / 引理 `range_mapIncl`

English:
lemma range_mapIncl
  given: (p : Submodule R P) (q : Submodule R Q)
  proof: by
  simp_rw [mapIncl, range_map, Submodule.range_subtype]

中文:
引理 range_mapIncl
  条件: (p : 子模 R P) (q : 子模 R Q)
  证明: by
  simp_rw [mapIncl, range_map, Submodule.range_subtype]

Depends on / 依赖: Submodule, Submodule.range_subtype, mapIncl, range_map, range_subtype, simp_rw
-/
lemma range_mapIncl (p : Submodule R P) (q : Submodule R Q) :
    LinearMap.range (mapIncl p q) = .map₂ (mk R _ _) p q := by
  simp_rw [mapIncl, range_map, Submodule.range_subtype]

/--
theorem `map₂_eq_range_lift_comp_mapIncl` / 定理 `map₂_eq_range_lift_comp_mapIncl`

English:
theorem map₂_eq_range_lift_comp_mapIncl
  statement: (f : P ->ₗ[R] Q ->ₗ[R] M)
  proof: by
  simp_rw [LinearMap.range_comp, range_mapIncl, Submodule.map_map₂]
  rfl

中文:
定理 map₂_eq_range_lift_comp_mapIncl
  结论: (f : P ->ₗ[R] Q ->ₗ[R] M)
  证明: by
  simp_rw [LinearMap.range_comp, range_mapIncl, Submodule.map_map₂]
  rfl

Depends on / 依赖: LinearMap, LinearMap.range_comp, Submodule, Submodule.map_map, range_comp, range_mapIncl, simp_rw
-/
theorem map₂_eq_range_lift_comp_mapIncl (f : P ->ₗ[R] Q ->ₗ[R] M)
    (p : Submodule R P) (q : Submodule R Q) :
    Submodule.map₂ f p q = LinearMap.range (lift f ∘ₗ mapIncl p q) := by
  simp_rw [LinearMap.range_comp, range_mapIncl, Submodule.map_map₂]
  rfl

section

variable {P' Q' : Type*}
variable [AddCommMonoid P'] [Module R P']
variable [AddCommMonoid Q'] [Module R Q']
variable [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

/--
theorem `map_comp` / 定理 `map_comp`

English:
theorem map_comp
  statement: (f₂ : M₂ ->ₛₗ[σ₂₃] M₃) (g₂ : N₂ ->ₛₗ[σ₂₃] N₃)
  proof: ext' fun _ _ => rfl

中文:
定理 map_comp
  结论: (f₂ : M₂ ->ₛₗ[σ₂₃] M₃) (g₂ : N₂ ->ₛₗ[σ₂₃] N₃)
  证明: ext' fun _ _ => rfl
-/
theorem map_comp (f₂ : M₂ ->ₛₗ[σ₂₃] M₃) (g₂ : N₂ ->ₛₗ[σ₂₃] N₃)
    (f₁ : M ->ₛₗ[σ₁₂] M₂) (g₁ : N ->ₛₗ[σ₁₂] N₂) :
    map (f₂ ∘ₛₗ f₁) (g₂ ∘ₛₗ g₁) = (map f₂ g₂) ∘ₛₗ (map f₁ g₁) := ext' fun _ _ => rfl

/--
theorem `map_map` / 定理 `map_map`

English:
theorem map_map
  statement: (f₂ : M₂ ->ₛₗ[σ₂₃] M₃) (g₂ : N₂ ->ₛₗ[σ₂₃] N₃)
  proof: DFunLike.congr_fun (map_comp ..).symm x

中文:
定理 map_map
  结论: (f₂ : M₂ ->ₛₗ[σ₂₃] M₃) (g₂ : N₂ ->ₛₗ[σ₂₃] N₃)
  证明: DFunLike.congr_fun (map_comp ..).symm x

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun, map_comp
-/
theorem map_map (f₂ : M₂ ->ₛₗ[σ₂₃] M₃) (g₂ : N₂ ->ₛₗ[σ₂₃] N₃)
    (f₁ : M ->ₛₗ[σ₁₂] M₂) (g₁ : N ->ₛₗ[σ₁₂] N₂) (x : M otimes[R] N) :
    map f₂ g₂ (map f₁ g₁ x) = map (f₂ ∘ₛₗ f₁) (g₂ ∘ₛₗ g₁) x :=
  DFunLike.congr_fun (map_comp ..).symm x

/--
lemma `range_map_mono` / 引理 `range_map_mono`

English:
lemma range_map_mono
  statement: [Module R M₂] [Module R M₃] [Module R N₂] [Module R N₃]
  proof: by
  simp_rw [range_map]
  exact Submodule.map₂_le_map₂ hab hcd

中文:
引理 range_map_mono
  结论: [模 R M₂] [模 R M₃] [模 R N₂] [模 R N₃]
  证明: by
  simp_rw [range_map]
  exact Submodule.map₂_le_map₂ hab hcd

Depends on / 依赖: Submodule, Submodule.map, range_map, simp_rw
-/
lemma range_map_mono [Module R M₂] [Module R M₃] [Module R N₂] [Module R N₃]
    {a : M ->ₗ[R] M₂} {b : M₃ ->ₗ[R] M₂} {c : N ->ₗ[R] N₂} {d : N₃ ->ₗ[R] N₂}
    (hab : range a <= range b) (hcd : range c <= range d) : range (map a c) <= range (map b d) := by
  simp_rw [range_map]
  exact Submodule.map₂_le_map₂ hab hcd

/--
lemma `range_mapIncl_mono` / 引理 `range_mapIncl_mono`

English:
lemma range_mapIncl_mono
  given: {p p' : Submodule R P} {q q' : Submodule R Q} (hp : p <= p') (hq : q <= q')
  proof: range_map_mono (by simpa) (by simpa)

中文:
引理 range_mapIncl_mono
  条件: {p p' : 子模 R P} {q q' : 子模 R Q} (hp : p <= p') (hq : q <= q')
  证明: range_map_mono (by simpa) (by simpa)

Depends on / 依赖: range_map_mono
-/
lemma range_mapIncl_mono {p p' : Submodule R P} {q q' : Submodule R Q} (hp : p <= p') (hq : q <= q') :
    LinearMap.range (mapIncl p q) <= LinearMap.range (mapIncl p' q') :=
  range_map_mono (by simpa) (by simpa)

/--
theorem `lift_comp_map` / 定理 `lift_comp_map`

English:
theorem lift_comp_map
  given: (i : M₂ ->ₛₗ[σ₂₃] N₂ ->ₛₗ[σ₂₃] P₃) (f : M ->ₛₗ[σ₁₂] M₂) (g : N ->ₛₗ[σ₁₂] N₂)
  proof: ext' fun _ _ => rfl

中文:
定理 lift_comp_map
  条件: (i : M₂ ->ₛₗ[σ₂₃] N₂ ->ₛₗ[σ₂₃] P₃) (f : M ->ₛₗ[σ₁₂] M₂) (g : N ->ₛₗ[σ₁₂] N₂)
  证明: ext' fun _ _ => rfl
-/
theorem lift_comp_map (i : M₂ ->ₛₗ[σ₂₃] N₂ ->ₛₗ[σ₂₃] P₃) (f : M ->ₛₗ[σ₁₂] M₂) (g : N ->ₛₗ[σ₁₂] N₂) :
    (lift i).comp (map f g) = lift ((i.comp f).compl₂ g) :=
  ext' fun _ _ => rfl

attribute [local ext high] ext

@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  statement: map (id : M ->ₗ[R] M) (id : N ->ₗ[R] N) = .id
  proof: by
  ext
  simp only [mk_apply, id_coe, compr₂ₛₗ_apply, _root_.id, map_tmul]

@[simp]

中文:
定理 map_id
  结论: map (id : M ->ₗ[R] M) (id : N ->ₗ[R] N) = .id
  证明: by
  ext
  simp only [mk_apply, id_coe, compr₂ₛₗ_apply, _root_.id, map_tmul]

@[simp]

Depends on / 依赖: _root_, _root_.id, id_coe, map_tmul, mk_apply
-/
theorem map_id : map (id : M ->ₗ[R] M) (id : N ->ₗ[R] N) = .id := by
  ext
  simp only [mk_apply, id_coe, compr₂ₛₗ_apply, _root_.id, map_tmul]

@[simp]
/--
theorem `map_one` / 定理 `map_one`

English:
theorem map_one
  statement: map (1 : M ->ₗ[R] M) (1 : N ->ₗ[R] N) = 1
  proof: map_id

中文:
定理 map_one
  结论: map (1 : M ->ₗ[R] M) (1 : N ->ₗ[R] N) = 1
  证明: map_id
-/
protected theorem map_one : map (1 : M ->ₗ[R] M) (1 : N ->ₗ[R] N) = 1 :=
  map_id

/--
theorem `map_mul` / 定理 `map_mul`

English:
theorem map_mul
  given: (f₁ f₂ : M ->ₗ[R] M) (g₁ g₂ : N ->ₗ[R] N)
  proof: map_comp ..

@[simp]

中文:
定理 map_mul
  条件: (f₁ f₂ : M ->ₗ[R] M) (g₁ g₂ : N ->ₗ[R] N)
  证明: map_comp ..

@[simp]
-/
protected theorem map_mul (f₁ f₂ : M ->ₗ[R] M) (g₁ g₂ : N ->ₗ[R] N) :
    map (f₁ * f₂) (g₁ * g₂) = map f₁ g₁ * map f₂ g₂ :=
  map_comp ..

@[simp]
/--
theorem `map_pow` / 定理 `map_pow`

English:
theorem map_pow
  given: (f : M ->ₗ[R] M) (g : N ->ₗ[R] N) (n : Nat)
  proof: by
  induction n with
  | zero => simp only [pow_zero, TensorProduct.map_one]
  | succ n ih => simp only [pow_succ', ih, TensorProduct.map_mul]

中文:
定理 map_pow
  条件: (f : M ->ₗ[R] M) (g : N ->ₗ[R] N) (n : 自然数)
  证明: by
  induction n with
  | zero => simp only [pow_zero, TensorProduct.map_one]
  | succ n ih => simp only [pow_succ', ih, TensorProduct.map_mul]
-/
protected theorem map_pow (f : M ->ₗ[R] M) (g : N ->ₗ[R] N) (n : Nat) :
    map f g ^ n = map (f ^ n) (g ^ n) := by
  induction n with
  | zero => simp only [pow_zero, TensorProduct.map_one]
  | succ n ih => simp only [pow_succ', ih, TensorProduct.map_mul]

/--
theorem `map_add_left` / 定理 `map_add_left`

English:
theorem map_add_left
  given: (f₁ f₂ : M ->ₛₗ[σ₁₂] M₂) (g : N ->ₛₗ[σ₁₂] N₂)
  proof: by
  ext
  simp only [add_tmul, compr₂ₛₗ_apply, mk_apply, map_tmul, add_apply]

中文:
定理 map_add_left
  条件: (f₁ f₂ : M ->ₛₗ[σ₁₂] M₂) (g : N ->ₛₗ[σ₁₂] N₂)
  证明: by
  ext
  simp only [add_tmul, compr₂ₛₗ_apply, mk_apply, map_tmul, add_apply]

Depends on / 依赖: add_apply, add_tmul, map_tmul, mk_apply
-/
theorem map_add_left (f₁ f₂ : M ->ₛₗ[σ₁₂] M₂) (g : N ->ₛₗ[σ₁₂] N₂) :
    map (f₁ + f₂) g = map f₁ g + map f₂ g := by
  ext
  simp only [add_tmul, compr₂ₛₗ_apply, mk_apply, map_tmul, add_apply]

/--
theorem `map_add_right` / 定理 `map_add_right`

English:
theorem map_add_right
  given: (f : M ->ₛₗ[σ₁₂] M₂) (g₁ g₂ : N ->ₛₗ[σ₁₂] N₂)
  proof: by
  ext
  simp only [tmul_add, compr₂ₛₗ_apply, mk_apply, map_tmul, add_apply]

中文:
定理 map_add_right
  条件: (f : M ->ₛₗ[σ₁₂] M₂) (g₁ g₂ : N ->ₛₗ[σ₁₂] N₂)
  证明: by
  ext
  simp only [tmul_add, compr₂ₛₗ_apply, mk_apply, map_tmul, add_apply]

Depends on / 依赖: add_apply, map_tmul, mk_apply, tmul_add
-/
theorem map_add_right (f : M ->ₛₗ[σ₁₂] M₂) (g₁ g₂ : N ->ₛₗ[σ₁₂] N₂) :
    map f (g₁ + g₂) = map f g₁ + map f g₂ := by
  ext
  simp only [tmul_add, compr₂ₛₗ_apply, mk_apply, map_tmul, add_apply]

/--
theorem `map_smul_left` / 定理 `map_smul_left`

English:
theorem map_smul_left
  given: (r : R₂) (f : M ->ₛₗ[σ₁₂] M₂) (g : N ->ₛₗ[σ₁₂] N₂)
  proof: by
  ext
  simp only [smul_tmul, compr₂ₛₗ_apply, mk_apply, map_tmul, smul_apply, tmul_smul]

中文:
定理 map_smul_left
  条件: (r : R₂) (f : M ->ₛₗ[σ₁₂] M₂) (g : N ->ₛₗ[σ₁₂] N₂)
  证明: by
  ext
  simp only [smul_tmul, compr₂ₛₗ_apply, mk_apply, map_tmul, smul_apply, tmul_smul]

Depends on / 依赖: map_tmul, mk_apply, smul_apply, smul_tmul, tmul_smul
-/
theorem map_smul_left (r : R₂) (f : M ->ₛₗ[σ₁₂] M₂) (g : N ->ₛₗ[σ₁₂] N₂) :
    map (r • f) g = r • map f g := by
  ext
  simp only [smul_tmul, compr₂ₛₗ_apply, mk_apply, map_tmul, smul_apply, tmul_smul]

/--
theorem `map_smul_right` / 定理 `map_smul_right`

English:
theorem map_smul_right
  given: (r : R₂) (f : M ->ₛₗ[σ₁₂] M₂) (g : N ->ₛₗ[σ₁₂] N₂)
  proof: by
  ext
  simp only [compr₂ₛₗ_apply, mk_apply, map_tmul, smul_apply, tmul_smul]

中文:
定理 map_smul_right
  条件: (r : R₂) (f : M ->ₛₗ[σ₁₂] M₂) (g : N ->ₛₗ[σ₁₂] N₂)
  证明: by
  ext
  simp only [compr₂ₛₗ_apply, mk_apply, map_tmul, smul_apply, tmul_smul]

Depends on / 依赖: map_tmul, mk_apply, smul_apply, tmul_smul
-/
theorem map_smul_right (r : R₂) (f : M ->ₛₗ[σ₁₂] M₂) (g : N ->ₛₗ[σ₁₂] N₂) :
    map f (r • g) = r • map f g := by
  ext
  simp only [compr₂ₛₗ_apply, mk_apply, map_tmul, smul_apply, tmul_smul]

variable (M N P M₂ N₂ σ₁₂)

/--
Definition of `mapBilinear` / `mapBilinear` 的定义

English:
definition mapBilinear
  signature: : (M ->ₛₗ[σ₁₂] M₂) ->ₗ[R₂] (N ->ₛₗ[σ₁₂] N₂) ->ₗ[R₂] M otimes[R] N ->ₛₗ[σ₁₂] M₂ otimes[R₂] N₂
  body: LinearMap.mk₂ R₂ map map_add_left map_smul_left map_add_right map_smul_right

中文:
定义 mapBilinear
  签名: : (M ->ₛₗ[σ₁₂] M₂) ->ₗ[R₂] (N ->ₛₗ[σ₁₂] N₂) ->ₗ[R₂] M otimes[R] N ->ₛₗ[σ₁₂] M₂ otimes[R₂] N₂
  定义体: LinearMap.mk₂ R₂ map map_add_left map_smul_left map_add_right map_smul_right

Depends on / 依赖: LinearMap, LinearMap.mk, map_add_left, map_add_right, map_smul_left, map_smul_right
-/
def mapBilinear : (M ->ₛₗ[σ₁₂] M₂) ->ₗ[R₂] (N ->ₛₗ[σ₁₂] N₂) ->ₗ[R₂] M otimes[R] N ->ₛₗ[σ₁₂] M₂ otimes[R₂] N₂ :=
  LinearMap.mk₂ R₂ map map_add_left map_smul_left map_add_right map_smul_right

/--
Definition of `lTensorHomToHomLTensor` / `lTensorHomToHomLTensor` 的定义

English:
definition lTensorHomToHomLTensor
  signature: : M₂ otimes[R₂] (P ->ₛₗ[σ₁₂] N₂) ->ₗ[R₂] P ->ₛₗ[σ₁₂] M₂ otimes[R₂] N₂
  body: TensorProduct.lift (llcomp _ P N₂ _ ∘ₛₗ mk R₂ M₂ N₂)

中文:
定义 lTensorHomToHomLTensor
  签名: : M₂ otimes[R₂] (P ->ₛₗ[σ₁₂] N₂) ->ₗ[R₂] P ->ₛₗ[σ₁₂] M₂ otimes[R₂] N₂
  定义体: TensorProduct.lift (llcomp _ P N₂ _ ∘ₛₗ mk R₂ M₂ N₂)

Depends on / 依赖: TensorProduct, TensorProduct.lift, llcomp
-/
def lTensorHomToHomLTensor : M₂ otimes[R₂] (P ->ₛₗ[σ₁₂] N₂) ->ₗ[R₂] P ->ₛₗ[σ₁₂] M₂ otimes[R₂] N₂ :=
  TensorProduct.lift (llcomp _ P N₂ _ ∘ₛₗ mk R₂ M₂ N₂)

/--
Definition of `rTensorHomToHomRTensor` / `rTensorHomToHomRTensor` 的定义

English:
definition rTensorHomToHomRTensor
  signature: : (P ->ₛₗ[σ₁₂] M₂) otimes[R₂] N₂ ->ₗ[R₂] P ->ₛₗ[σ₁₂] M₂ otimes[R₂] N₂
  body: TensorProduct.lift (llcomp _ P M₂ _ ∘ₗ (mk R₂ M₂ N₂).flip).flip

中文:
定义 rTensorHomToHomRTensor
  签名: : (P ->ₛₗ[σ₁₂] M₂) otimes[R₂] N₂ ->ₗ[R₂] P ->ₛₗ[σ₁₂] M₂ otimes[R₂] N₂
  定义体: TensorProduct.lift (llcomp _ P M₂ _ ∘ₗ (mk R₂ M₂ N₂).flip).flip

Depends on / 依赖: TensorProduct, TensorProduct.lift, llcomp
-/
def rTensorHomToHomRTensor : (P ->ₛₗ[σ₁₂] M₂) otimes[R₂] N₂ ->ₗ[R₂] P ->ₛₗ[σ₁₂] M₂ otimes[R₂] N₂ :=
  TensorProduct.lift (llcomp _ P M₂ _ ∘ₗ (mk R₂ M₂ N₂).flip).flip

/--
Definition of `homTensorHomMap` / `homTensorHomMap` 的定义

English:
definition homTensorHomMap
  signature: : (M ->ₛₗ[σ₁₂] M₂) otimes[R₂] (N ->ₛₗ[σ₁₂] N₂) ->ₗ[R₂] M otimes[R] N ->ₛₗ[σ₁₂] M₂ otimes[R₂] N₂
  body: lift (mapBilinear σ₁₂ M N M₂ N₂)

中文:
定义 homTensorHomMap
  签名: : (M ->ₛₗ[σ₁₂] M₂) otimes[R₂] (N ->ₛₗ[σ₁₂] N₂) ->ₗ[R₂] M otimes[R] N ->ₛₗ[σ₁₂] M₂ otimes[R₂] N₂
  定义体: lift (mapBilinear σ₁₂ M N M₂ N₂)

Depends on / 依赖: mapBilinear
-/
def homTensorHomMap : (M ->ₛₗ[σ₁₂] M₂) otimes[R₂] (N ->ₛₗ[σ₁₂] N₂) ->ₗ[R₂] M otimes[R] N ->ₛₗ[σ₁₂] M₂ otimes[R₂] N₂ :=
  lift (mapBilinear σ₁₂ M N M₂ N₂)

variable {M N P M₂ N₂ σ₁₂}

/--
Definition of `map₂` / `map₂` 的定义

English:
definition map₂
  signature: (f : M ->ₛₗ[σ₁₃] M₂ ->ₛₗ[σ₂₃] M₃) (g : N ->ₛₗ[σ₁₃] N₂ ->ₛₗ[σ₂₃] N₃)
  body: homTensorHomMap σ₂₃ _ _ _ _ ∘ₛₗ map f g

@[simp]

中文:
定义 map₂
  签名: (f : M ->ₛₗ[σ₁₃] M₂ ->ₛₗ[σ₂₃] M₃) (g : N ->ₛₗ[σ₁₃] N₂ ->ₛₗ[σ₂₃] N₃)
  定义体: homTensorHomMap σ₂₃ _ _ _ _ ∘ₛₗ map f g

@[simp]

Depends on / 依赖: homTensorHomMap
-/
def map₂ (f : M ->ₛₗ[σ₁₃] M₂ ->ₛₗ[σ₂₃] M₃) (g : N ->ₛₗ[σ₁₃] N₂ ->ₛₗ[σ₂₃] N₃) :
    M otimes[R] N ->ₛₗ[σ₁₃] M₂ otimes[R₂] N₂ ->ₛₗ[σ₂₃] M₃ otimes[R₃] N₃ :=
  homTensorHomMap σ₂₃ _ _ _ _ ∘ₛₗ map f g

@[simp]
/--
theorem `mapBilinear_apply` / 定理 `mapBilinear_apply`

English:
theorem mapBilinear_apply
  given: (f : M ->ₛₗ[σ₁₂] M₂) (g : N ->ₛₗ[σ₁₂] N₂)
  proof: rfl

@[simp]

中文:
定理 mapBilinear_apply
  条件: (f : M ->ₛₗ[σ₁₂] M₂) (g : N ->ₛₗ[σ₁₂] N₂)
  证明: rfl

@[simp]
-/
theorem mapBilinear_apply (f : M ->ₛₗ[σ₁₂] M₂) (g : N ->ₛₗ[σ₁₂] N₂) :
    mapBilinear σ₁₂ M N M₂ N₂ f g = map f g :=
  rfl

@[simp]
/--
theorem `lTensorHomToHomLTensor_apply` / 定理 `lTensorHomToHomLTensor_apply`

English:
theorem lTensorHomToHomLTensor_apply
  given: (m₂ : M₂) (f : P ->ₛₗ[σ₁₂] N₂) (p : P)
  proof: rfl

@[simp]

中文:
定理 lTensorHomToHomLTensor_apply
  条件: (m₂ : M₂) (f : P ->ₛₗ[σ₁₂] N₂) (p : P)
  证明: rfl

@[simp]
-/
theorem lTensorHomToHomLTensor_apply (m₂ : M₂) (f : P ->ₛₗ[σ₁₂] N₂) (p : P) :
    lTensorHomToHomLTensor _ P M₂ N₂ (m₂ otimesₜ f) p = m₂ otimesₜ f p :=
  rfl

@[simp]
/--
theorem `rTensorHomToHomRTensor_apply` / 定理 `rTensorHomToHomRTensor_apply`

English:
theorem rTensorHomToHomRTensor_apply
  given: (f : P ->ₛₗ[σ₁₂] M₂) (n₂ : N₂) (p : P)
  proof: rfl

@[simp]

中文:
定理 rTensorHomToHomRTensor_apply
  条件: (f : P ->ₛₗ[σ₁₂] M₂) (n₂ : N₂) (p : P)
  证明: rfl

@[simp]
-/
theorem rTensorHomToHomRTensor_apply (f : P ->ₛₗ[σ₁₂] M₂) (n₂ : N₂) (p : P) :
    rTensorHomToHomRTensor _ P M₂ N₂ (f otimesₜ n₂) p = f p otimesₜ n₂ :=
  rfl

@[simp]
/--
theorem `homTensorHomMap_apply` / 定理 `homTensorHomMap_apply`

English:
theorem homTensorHomMap_apply
  given: (f : M ->ₛₗ[σ₁₂] M₂) (g : N ->ₛₗ[σ₁₂] N₂)
  proof: rfl

@[simp]

中文:
定理 homTensorHomMap_apply
  条件: (f : M ->ₛₗ[σ₁₂] M₂) (g : N ->ₛₗ[σ₁₂] N₂)
  证明: rfl

@[simp]
-/
theorem homTensorHomMap_apply (f : M ->ₛₗ[σ₁₂] M₂) (g : N ->ₛₗ[σ₁₂] N₂) :
    homTensorHomMap _ M N M₂ N₂ (f otimesₜ g) = map f g :=
  rfl

@[simp]
/--
theorem `map₂_apply_tmul` / 定理 `map₂_apply_tmul`

English:
theorem map₂_apply_tmul
  statement: (f : M ->ₛₗ[σ₁₃] M₂ ->ₛₗ[σ₂₃] M₃) (g : N ->ₛₗ[σ₁₃] N₂ ->ₛₗ[σ₂₃] N₃)
  proof: rfl

@[simp]

中文:
定理 map₂_apply_tmul
  结论: (f : M ->ₛₗ[σ₁₃] M₂ ->ₛₗ[σ₂₃] M₃) (g : N ->ₛₗ[σ₁₃] N₂ ->ₛₗ[σ₂₃] N₃)
  证明: rfl

@[simp]
-/
theorem map₂_apply_tmul (f : M ->ₛₗ[σ₁₃] M₂ ->ₛₗ[σ₂₃] M₃) (g : N ->ₛₗ[σ₁₃] N₂ ->ₛₗ[σ₂₃] N₃)
    (m : M) (n : N) :
    map₂ f g (m otimesₜ n) = map (f m) (g n) := rfl

@[simp]
/--
theorem `map_zero_left` / 定理 `map_zero_left`

English:
theorem map_zero_left
  given: (g : N ->ₛₗ[σ₁₂] N₂)
  statement: map (0 : M ->ₛₗ[σ₁₂] M₂) g = 0
  proof: (mapBilinear _ M N M₂ N₂).map_zero₂ _

@[simp]

中文:
定理 map_zero_left
  条件: (g : N ->ₛₗ[σ₁₂] N₂)
  结论: map (0 : M ->ₛₗ[σ₁₂] M₂) g = 0
  证明: (mapBilinear _ M N M₂ N₂).map_zero₂ _

@[simp]

Depends on / 依赖: mapBilinear
-/
theorem map_zero_left (g : N ->ₛₗ[σ₁₂] N₂) : map (0 : M ->ₛₗ[σ₁₂] M₂) g = 0 :=
  (mapBilinear _ M N M₂ N₂).map_zero₂ _

@[simp]
/--
theorem `map_zero_right` / 定理 `map_zero_right`

English:
theorem map_zero_right
  given: (f : M ->ₛₗ[σ₁₂] M₂)
  statement: map f (0 : N ->ₛₗ[σ₁₂] N₂) = 0
  proof: (mapBilinear _ M N M₂ N₂ f).map_zero

中文:
定理 map_zero_right
  条件: (f : M ->ₛₗ[σ₁₂] M₂)
  结论: map f (0 : N ->ₛₗ[σ₁₂] N₂) = 0
  证明: (mapBilinear _ M N M₂ N₂ f).map_zero

Depends on / 依赖: mapBilinear, map_zero
-/
theorem map_zero_right (f : M ->ₛₗ[σ₁₂] M₂) : map f (0 : N ->ₛₗ[σ₁₂] N₂) = 0 :=
  (mapBilinear _ M N M₂ N₂ f).map_zero

end

variable {σ₂₁ : R₂ ->+* R} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]

/--
Definition of `congr` / `congr` 的定义

English:
definition congr
  signature: (f : M ≃ₛₗ[σ₁₂] M₂) (g : N ≃ₛₗ[σ₁₂] N₂)
  body: LinearEquiv.ofLinearMap (map f g) (map f.symm g.symm)
    (ext' fun m n => by simp)
    (ext' fun m n => by simp)

@[simp]

中文:
定义 congr
  签名: (f : M ≃ₛₗ[σ₁₂] M₂) (g : N ≃ₛₗ[σ₁₂] N₂)
  定义体: LinearEquiv.ofLinearMap (map f g) (map f.symm g.symm)
    (ext' fun m n => by simp)
    (ext' fun m n => by simp)

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.ofLinearMap, f.symm, g.symm, ofLinearMap
-/
def congr (f : M ≃ₛₗ[σ₁₂] M₂) (g : N ≃ₛₗ[σ₁₂] N₂) : M otimes[R] N ≃ₛₗ[σ₁₂] M₂ otimes[R₂] N₂ :=
  LinearEquiv.ofLinearMap (map f g) (map f.symm g.symm)
    (ext' fun m n => by simp)
    (ext' fun m n => by simp)

@[simp]
/--
lemma `toLinearMap_congr` / 引理 `toLinearMap_congr`

English:
lemma toLinearMap_congr
  given: (f : M ≃ₛₗ[σ₁₂] M₂) (g : N ≃ₛₗ[σ₁₂] N₂)
  proof: rfl

@[simp]

中文:
引理 toLinearMap_congr
  条件: (f : M ≃ₛₗ[σ₁₂] M₂) (g : N ≃ₛₗ[σ₁₂] N₂)
  证明: rfl

@[simp]
-/
lemma toLinearMap_congr (f : M ≃ₛₗ[σ₁₂] M₂) (g : N ≃ₛₗ[σ₁₂] N₂) :
    (congr f g).toLinearMap = map f g := rfl

@[simp]
/--
theorem `congr_tmul` / 定理 `congr_tmul`

English:
theorem congr_tmul
  given: (f : M ≃ₛₗ[σ₁₂] M₂) (g : N ≃ₛₗ[σ₁₂] N₂) (m : M) (n : N)
  proof: rfl

@[simp]

中文:
定理 congr_tmul
  条件: (f : M ≃ₛₗ[σ₁₂] M₂) (g : N ≃ₛₗ[σ₁₂] N₂) (m : M) (n : N)
  证明: rfl

@[simp]
-/
theorem congr_tmul (f : M ≃ₛₗ[σ₁₂] M₂) (g : N ≃ₛₗ[σ₁₂] N₂) (m : M) (n : N) :
    congr f g (m otimesₜ n) = f m otimesₜ g n :=
  rfl

@[simp]
/--
theorem `congr_symm_tmul` / 定理 `congr_symm_tmul`

English:
theorem congr_symm_tmul
  given: (f : M ≃ₛₗ[σ₁₂] M₂) (g : N ≃ₛₗ[σ₁₂] N₂) (p : M₂) (q : N₂)
  proof: rfl

中文:
定理 congr_symm_tmul
  条件: (f : M ≃ₛₗ[σ₁₂] M₂) (g : N ≃ₛₗ[σ₁₂] N₂) (p : M₂) (q : N₂)
  证明: rfl
-/
theorem congr_symm_tmul (f : M ≃ₛₗ[σ₁₂] M₂) (g : N ≃ₛₗ[σ₁₂] N₂) (p : M₂) (q : N₂) :
    (congr f g).symm (p otimesₜ q) = f.symm p otimesₜ g.symm q :=
  rfl

/--
theorem `congr_symm` / 定理 `congr_symm`

English:
theorem congr_symm
  given: (f : M ≃ₛₗ[σ₁₂] M₂) (g : N ≃ₛₗ[σ₁₂] N₂)
  proof: rfl

中文:
定理 congr_symm
  条件: (f : M ≃ₛₗ[σ₁₂] M₂) (g : N ≃ₛₗ[σ₁₂] N₂)
  证明: rfl
-/
theorem congr_symm (f : M ≃ₛₗ[σ₁₂] M₂) (g : N ≃ₛₗ[σ₁₂] N₂) :
    (congr f g).symm = congr f.symm g.symm := rfl

/--
theorem `congr_refl_refl` / 定理 `congr_refl_refl`

English:
theorem congr_refl_refl
  statement: congr (.refl R M) (.refl R N) = .refl R _
  proof: LinearEquiv.toLinearMap_injective ext' fun _ _ => rfl

中文:
定理 congr_refl_refl
  结论: congr (.refl R M) (.refl R N) = .refl R _
  证明: LinearEquiv.toLinearMap_injective ext' fun _ _ => rfl
-/
@[simp] theorem congr_refl_refl : congr (.refl R M) (.refl R N) = .refl R _ :=
LinearEquiv.toLinearMap_injective ext' fun _ _ => rfl

section congr_congr
variable {σ₃₂ : R₃ ->+* R₂} [RingHomInvPair σ₂₃ σ₃₂] [RingHomInvPair σ₃₂ σ₂₃]
  {σ₃₁ : R₃ ->+* R} [RingHomInvPair σ₁₃ σ₃₁] [RingHomInvPair σ₃₁ σ₁₃]
  [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomCompTriple σ₃₂ σ₂₁ σ₃₁]
  (f₂ : M₂ ≃ₛₗ[σ₂₃] M₃) (g₂ : N₂ ≃ₛₗ[σ₂₃] N₃) (f₁ : M ≃ₛₗ[σ₁₂] M₂) (g₁ : N ≃ₛₗ[σ₁₂] N₂)

/--
theorem `congr_trans` / 定理 `congr_trans`

English:
theorem congr_trans
  statement: congr (f₁.trans f₂) (g₁.trans g₂) = (congr f₁ g₁).trans (congr f₂ g₂)
  proof: LinearEquiv.toLinearMap_injective map_comp _ _ _ _

中文:
定理 congr_trans
  结论: congr (f₁.trans f₂) (g₁.trans g₂) = (congr f₁ g₁).trans (congr f₂ g₂)
  证明: LinearEquiv.toLinearMap_injective map_comp _ _ _ _

Depends on / 依赖: LinearEquiv, LinearEquiv.toLinearMap_injective, map_comp, toLinearMap_injective
-/
theorem congr_trans : congr (f₁.trans f₂) (g₁.trans g₂) = (congr f₁ g₁).trans (congr f₂ g₂) :=
LinearEquiv.toLinearMap_injective map_comp _ _ _ _

/--
theorem `congr_congr` / 定理 `congr_congr`

English:
theorem congr_congr
  given: (x : M otimes[R] N)
  proof: DFunLike.congr_fun (congr_trans ..).symm x

中文:
定理 congr_congr
  条件: (x : M otimes[R] N)
  证明: DFunLike.congr_fun (congr_trans ..).symm x

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun, congr_trans
-/
theorem congr_congr (x : M otimes[R] N) :
    congr f₂ g₂ (congr f₁ g₁ x) = congr (f₁.trans f₂) (g₁.trans g₂) x :=
  DFunLike.congr_fun (congr_trans ..).symm x

end congr_congr

/--
theorem `congr_mul` / 定理 `congr_mul`

English:
theorem congr_mul
  given: (f : M ≃ₗ[R] M) (g : N ≃ₗ[R] N) (f' : M ≃ₗ[R] M) (g' : N ≃ₗ[R] N)
  proof: congr_trans _ _ _ _

中文:
定理 congr_mul
  条件: (f : M ≃ₗ[R] M) (g : N ≃ₗ[R] N) (f' : M ≃ₗ[R] M) (g' : N ≃ₗ[R] N)
  证明: congr_trans _ _ _ _

Depends on / 依赖: congr_trans
-/
theorem congr_mul (f : M ≃ₗ[R] M) (g : N ≃ₗ[R] N) (f' : M ≃ₗ[R] M) (g' : N ≃ₗ[R] N) :
    congr (f * f') (g * g') = congr f g * congr f' g' := congr_trans _ _ _ _

/--
theorem `congr_pow` / 定理 `congr_pow`

English:
theorem congr_pow
  given: (f : M ≃ₗ[R] M) (g : N ≃ₗ[R] N) (n : Nat)
  proof: by
  induction n with
  | zero => exact congr_refl_refl.symm
  | succ n ih => simp_rw [pow_succ, ih, congr_mul]

中文:
定理 congr_pow
  条件: (f : M ≃ₗ[R] M) (g : N ≃ₗ[R] N) (n : 自然数)
  证明: by
  induction n with
  | zero => exact congr_refl_refl.symm
  | succ n ih => simp_rw [pow_succ, ih, congr_mul]
-/
@[simp] theorem congr_pow (f : M ≃ₗ[R] M) (g : N ≃ₗ[R] N) (n : Nat) :
    congr f g ^ n = congr (f ^ n) (g ^ n) := by
  induction n with
  | zero => exact congr_refl_refl.symm
  | succ n ih => simp_rw [pow_succ, ih, congr_mul]

/--
theorem `congr_zpow` / 定理 `congr_zpow`

English:
theorem congr_zpow
  given: (f : M ≃ₗ[R] M) (g : N ≃ₗ[R] N) (n : Int)
  proof: by
  cases n with
  | ofNat n => exact congr_pow _ _ _
  | negSucc n => simp_rw [zpow_negSucc, congr_pow]; exact congr_symm _ _

中文:
定理 congr_zpow
  条件: (f : M ≃ₗ[R] M) (g : N ≃ₗ[R] N) (n : 整数)
  证明: by
  cases n with
  | ofNat n => exact congr_pow _ _ _
  | negSucc n => simp_rw [zpow_negSucc, congr_pow]; exact congr_symm _ _
-/
@[simp] theorem congr_zpow (f : M ≃ₗ[R] M) (g : N ≃ₗ[R] N) (n : Int) :
    congr f g ^ n = congr (f ^ n) (g ^ n) := by
  cases n with
  | ofNat n => exact congr_pow _ _ _
  | negSucc n => simp_rw [zpow_negSucc, congr_pow]; exact congr_symm _ _

/--
lemma `map_bijective` / 引理 `map_bijective`

English:
lemma map_bijective
  statement: {f : M ->ₗ[R] N} {g : P ->ₗ[R] Q}
  proof: (TensorProduct.congr (.ofBijective f hf) (.ofBijective g hg)).bijective

universe u in

中文:
引理 map_bijective
  结论: {f : M ->ₗ[R] N} {g : P ->ₗ[R] Q}
  证明: (TensorProduct.congr (.ofBijective f hf) (.ofBijective g hg)).bijective

universe u in

Depends on / 依赖: TensorProduct, TensorProduct.congr, bijective, ofBijective
-/
lemma map_bijective {f : M ->ₗ[R] N} {g : P ->ₗ[R] Q}
    (hf : Function.Bijective f) (hg : Function.Bijective g) :
    Function.Bijective (map f g) :=
  (TensorProduct.congr (.ofBijective f hf) (.ofBijective g hg)).bijective

universe u in
instance {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] [Small.{u} M] [Small.{u} N] : Small.{u} (M otimes[R] N) :=
  ⟨_, ⟨(TensorProduct.congr
    (Shrink.linearEquiv R M) (Shrink.linearEquiv R N)).symm.toEquiv⟩⟩

end TensorProduct

open scoped TensorProduct

variable [Module R P] [Module R Q]

namespace LinearMap

variable {N}

/--
Definition of `lTensor` / `lTensor` 的定义

English:
definition lTensor
  signature: (f : N ->ₗ[R] P)
  body: TensorProduct.map id f

中文:
定义 lTensor
  签名: (f : N ->ₗ[R] P)
  定义体: TensorProduct.map id f

Depends on / 依赖: TensorProduct, TensorProduct.map
-/
def lTensor (f : N ->ₗ[R] P) : M otimes[R] N ->ₗ[R] M otimes[R] P :=
  TensorProduct.map id f

/--
Definition of `rTensor` / `rTensor` 的定义

English:
definition rTensor
  signature: (f : N ->ₗ[R] P)
  body: TensorProduct.map f id

中文:
定义 rTensor
  签名: (f : N ->ₗ[R] P)
  定义体: TensorProduct.map f id

Depends on / 依赖: TensorProduct, TensorProduct.map
-/
def rTensor (f : N ->ₗ[R] P) : N otimes[R] M ->ₗ[R] P otimes[R] M :=
  TensorProduct.map f id

variable (g : P ->ₗ[R] Q) (f : N ->ₗ[R] P)

/--
theorem `lTensor_def` / 定理 `lTensor_def`

English:
theorem lTensor_def
  statement: f.lTensor M = TensorProduct.map LinearMap.id f
  proof: rfl

中文:
定理 lTensor_def
  结论: f.lTensor M = 张量积.map 线性映射.id f
  证明: rfl
-/
theorem lTensor_def : f.lTensor M = TensorProduct.map LinearMap.id f := rfl

/--
theorem `rTensor_def` / 定理 `rTensor_def`

English:
theorem rTensor_def
  statement: f.rTensor M = TensorProduct.map f LinearMap.id
  proof: rfl

@[simp]

中文:
定理 rTensor_def
  结论: f.rTensor M = 张量积.map f 线性映射.id
  证明: rfl

@[simp]
-/
theorem rTensor_def : f.rTensor M = TensorProduct.map f LinearMap.id := rfl

@[simp]
/--
theorem `lTensor_tmul` / 定理 `lTensor_tmul`

English:
theorem lTensor_tmul
  given: (m : M) (n : N)
  statement: f.lTensor M (m otimesₜ n) = m otimesₜ f n
  proof: rfl

@[simp]

中文:
定理 lTensor_tmul
  条件: (m : M) (n : N)
  结论: f.lTensor M (m otimesₜ n) = m otimesₜ f n
  证明: rfl

@[simp]
-/
theorem lTensor_tmul (m : M) (n : N) : f.lTensor M (m otimesₜ n) = m otimesₜ f n :=
  rfl

@[simp]
/--
theorem `rTensor_tmul` / 定理 `rTensor_tmul`

English:
theorem rTensor_tmul
  given: (m : M) (n : N)
  statement: f.rTensor M (n otimesₜ m) = f n otimesₜ m
  proof: rfl

@[simp]

中文:
定理 rTensor_tmul
  条件: (m : M) (n : N)
  结论: f.rTensor M (n otimesₜ m) = f n otimesₜ m
  证明: rfl

@[simp]
-/
theorem rTensor_tmul (m : M) (n : N) : f.rTensor M (n otimesₜ m) = f n otimesₜ m :=
  rfl

@[simp]
/--
theorem `lTensor_comp_mk` / 定理 `lTensor_comp_mk`

English:
theorem lTensor_comp_mk
  given: (m : M)
  proof: rfl

@[simp]

中文:
定理 lTensor_comp_mk
  条件: (m : M)
  证明: rfl

@[simp]
-/
theorem lTensor_comp_mk (m : M) :
    f.lTensor M ∘ₗ TensorProduct.mk R M N m = TensorProduct.mk R M P m ∘ₗ f :=
  rfl

@[simp]
/--
theorem `rTensor_comp_flip_mk` / 定理 `rTensor_comp_flip_mk`

English:
theorem rTensor_comp_flip_mk
  given: (m : M)
  proof: rfl

中文:
定理 rTensor_comp_flip_mk
  条件: (m : M)
  证明: rfl
-/
theorem rTensor_comp_flip_mk (m : M) :
    f.rTensor M ∘ₗ (TensorProduct.mk R N M).flip m = (TensorProduct.mk R P M).flip m ∘ₗ f :=
  rfl

/--
lemma `comm_comp_rTensor_comp_comm_eq` / 引理 `comm_comp_rTensor_comp_comm_eq`

English:
lemma comm_comp_rTensor_comp_comm_eq
  given: (g : N ->ₗ[R] P)
  proof: TensorProduct.ext rfl

中文:
引理 comm_comp_rTensor_comp_comm_eq
  条件: (g : N ->ₗ[R] P)
  证明: TensorProduct.ext rfl

Depends on / 依赖: TensorProduct, TensorProduct.ext
-/
lemma comm_comp_rTensor_comp_comm_eq (g : N ->ₗ[R] P) :
    TensorProduct.comm R P Q ∘ₗ rTensor Q g ∘ₗ TensorProduct.comm R Q N =
      lTensor Q g :=
  TensorProduct.ext rfl

/--
lemma `comm_comp_lTensor_comp_comm_eq` / 引理 `comm_comp_lTensor_comp_comm_eq`

English:
lemma comm_comp_lTensor_comp_comm_eq
  given: (g : N ->ₗ[R] P)
  proof: TensorProduct.ext rfl

中文:
引理 comm_comp_lTensor_comp_comm_eq
  条件: (g : N ->ₗ[R] P)
  证明: TensorProduct.ext rfl

Depends on / 依赖: TensorProduct, TensorProduct.ext
-/
lemma comm_comp_lTensor_comp_comm_eq (g : N ->ₗ[R] P) :
    TensorProduct.comm R Q P ∘ₗ lTensor Q g ∘ₗ TensorProduct.comm R N Q =
      rTensor Q g :=
  TensorProduct.ext rfl

/--
theorem `lTensor_inj_iff_rTensor_inj` / 定理 `lTensor_inj_iff_rTensor_inj`

English:
theorem lTensor_inj_iff_rTensor_inj
  proof: by
  simp [← comm_comp_rTensor_comp_comm_eq]

中文:
定理 lTensor_inj_iff_rTensor_inj
  证明: by
  simp [← comm_comp_rTensor_comp_comm_eq]

Depends on / 依赖: comm_comp_rTensor_comp_comm_eq
-/
theorem lTensor_inj_iff_rTensor_inj :
    Function.Injective (lTensor M f) ↔ Function.Injective (rTensor M f) := by
  simp [← comm_comp_rTensor_comp_comm_eq]

/--
theorem `lTensor_surj_iff_rTensor_surj` / 定理 `lTensor_surj_iff_rTensor_surj`

English:
theorem lTensor_surj_iff_rTensor_surj
  proof: by
  simp [← comm_comp_rTensor_comp_comm_eq]

中文:
定理 lTensor_surj_iff_rTensor_surj
  证明: by
  simp [← comm_comp_rTensor_comp_comm_eq]

Depends on / 依赖: comm_comp_rTensor_comp_comm_eq
-/
theorem lTensor_surj_iff_rTensor_surj :
    Function.Surjective (lTensor M f) ↔ Function.Surjective (rTensor M f) := by
  simp [← comm_comp_rTensor_comp_comm_eq]

/--
theorem `lTensor_bij_iff_rTensor_bij` / 定理 `lTensor_bij_iff_rTensor_bij`

English:
theorem lTensor_bij_iff_rTensor_bij
  proof: by
  simp [← comm_comp_rTensor_comp_comm_eq]

中文:
定理 lTensor_bij_iff_rTensor_bij
  证明: by
  simp [← comm_comp_rTensor_comp_comm_eq]

Depends on / 依赖: comm_comp_rTensor_comp_comm_eq
-/
theorem lTensor_bij_iff_rTensor_bij :
    Function.Bijective (lTensor M f) ↔ Function.Bijective (rTensor M f) := by
  simp [← comm_comp_rTensor_comp_comm_eq]

variable {M} in
/--
theorem `smul_lTensor` / 定理 `smul_lTensor`

English:
theorem smul_lTensor
  statement: {S : Type*} [CommSemiring S] [SMul R S] [Module S M] [IsScalarTower R S M]
  proof: have h : s • (f.lTensor M) = f.lTensor M ∘ₗ (LinearMap.lsmul S (M otimes[R] N) s).restrictScalars R :=
    TensorProduct.ext rfl
  congrFun (congrArg DFunLike.coe h) m

中文:
定理 smul_lTensor
  结论: {S : 类型} [交换半环 S] [标量乘法 R S] [模 S M] [标量塔 R S M]
  证明: have h : s • (f.lTensor M) = f.lTensor M ∘ₗ (LinearMap.lsmul S (M otimes[R] N) s).restrictScalars R :=
    TensorProduct.ext rfl
  congrFun (congrArg DFunLike.coe h) m

Depends on / 依赖: DFunLike, DFunLike.coe, LinearMap, LinearMap.lsmul, TensorProduct, TensorProduct.ext, f.lTensor, lTensor, otimes, restrictScalars
-/
theorem smul_lTensor {S : Type*} [CommSemiring S] [SMul R S] [Module S M] [IsScalarTower R S M]
    [SMulCommClass R S M] (s : S) (m : M otimes[R] N) : s • (f.lTensor M) m = (f.lTensor M) (s • m) :=
  have h : s • (f.lTensor M) = f.lTensor M ∘ₗ (LinearMap.lsmul S (M otimes[R] N) s).restrictScalars R :=
    TensorProduct.ext rfl
  congrFun (congrArg DFunLike.coe h) m

open TensorProduct

attribute [local ext high] TensorProduct.ext

/--
Definition of `lTensorHom` / `lTensorHom` 的定义

English:
definition lTensorHom
  signature: : (N ->ₗ[R] P) ->ₗ[R] M otimes[R] N ->ₗ[R] M otimes[R] P where
  body: lTensor M
  map_add' f g := by
    ext x y
    simp only [compr₂ₛₗ_apply, mk_apply, add_apply, lTensor_tmul, tmul_add]
  map_smul' r f := by
    dsimp
    ext x y
    simp only [compr₂ₛₗ_apply, mk_apply, tmul_smul, smul_apply, lTensor_tmul]

中文:
定义 lTensorHom
  签名: : (N ->ₗ[R] P) ->ₗ[R] M otimes[R] N ->ₗ[R] M otimes[R] P where
  定义体: lTensor M
  map_add' f g := by
    ext x y
    simp only [compr₂ₛₗ_apply, mk_apply, add_apply, lTensor_tmul, tmul_add]
  map_smul' r f := by
    dsimp
    ext x y
    simp only [compr₂ₛₗ_apply, mk_apply, tmul_smul, smul_apply, lTensor_tmul]

Depends on / 依赖: lTensor
-/
def lTensorHom : (N ->ₗ[R] P) ->ₗ[R] M otimes[R] N ->ₗ[R] M otimes[R] P where
  toFun := lTensor M
  map_add' f g := by
    ext x y
    simp only [compr₂ₛₗ_apply, mk_apply, add_apply, lTensor_tmul, tmul_add]
  map_smul' r f := by
    dsimp
    ext x y
    simp only [compr₂ₛₗ_apply, mk_apply, tmul_smul, smul_apply, lTensor_tmul]

/--
Definition of `rTensorHom` / `rTensorHom` 的定义

English:
definition rTensorHom
  signature: : (N ->ₗ[R] P) ->ₗ[R] N otimes[R] M ->ₗ[R] P otimes[R] M where
  body: f.rTensor M
  map_add' f g := by
    ext x y
    simp only [compr₂ₛₗ_apply, mk_apply, add_apply, rTensor_tmul, add_tmul]
  map_smul' r f := by
    dsimp
    ext x y
    simp only [compr₂ₛₗ_apply, mk_apply, smul_tmul, tmul_smul, smul_apply, rTensor_tmul]

@[simp]

中文:
定义 rTensorHom
  签名: : (N ->ₗ[R] P) ->ₗ[R] N otimes[R] M ->ₗ[R] P otimes[R] M where
  定义体: f.rTensor M
  map_add' f g := by
    ext x y
    simp only [compr₂ₛₗ_apply, mk_apply, add_apply, rTensor_tmul, add_tmul]
  map_smul' r f := by
    dsimp
    ext x y
    simp only [compr₂ₛₗ_apply, mk_apply, smul_tmul, tmul_smul, smul_apply, rTensor_tmul]

@[simp]

Depends on / 依赖: f.rTensor, rTensor
-/
def rTensorHom : (N ->ₗ[R] P) ->ₗ[R] N otimes[R] M ->ₗ[R] P otimes[R] M where
  toFun f := f.rTensor M
  map_add' f g := by
    ext x y
    simp only [compr₂ₛₗ_apply, mk_apply, add_apply, rTensor_tmul, add_tmul]
  map_smul' r f := by
    dsimp
    ext x y
    simp only [compr₂ₛₗ_apply, mk_apply, smul_tmul, tmul_smul, smul_apply, rTensor_tmul]

@[simp]
/--
theorem `coe_lTensorHom` / 定理 `coe_lTensorHom`

English:
theorem coe_lTensorHom
  statement: (lTensorHom M : (N ->ₗ[R] P) -> M otimes[R] N ->ₗ[R] M otimes[R] P) = lTensor M
  proof: rfl

@[simp]

中文:
定理 coe_lTensorHom
  结论: (lTensorHom M : (N ->ₗ[R] P) -> M otimes[R] N ->ₗ[R] M otimes[R] P) = lTensor M
  证明: rfl

@[simp]
-/
theorem coe_lTensorHom : (lTensorHom M : (N ->ₗ[R] P) -> M otimes[R] N ->ₗ[R] M otimes[R] P) = lTensor M :=
  rfl

@[simp]
/--
theorem `coe_rTensorHom` / 定理 `coe_rTensorHom`

English:
theorem coe_rTensorHom
  statement: (rTensorHom M : (N ->ₗ[R] P) -> N otimes[R] M ->ₗ[R] P otimes[R] M) = rTensor M
  proof: rfl

@[simp]

中文:
定理 coe_rTensorHom
  结论: (rTensorHom M : (N ->ₗ[R] P) -> N otimes[R] M ->ₗ[R] P otimes[R] M) = rTensor M
  证明: rfl

@[simp]
-/
theorem coe_rTensorHom : (rTensorHom M : (N ->ₗ[R] P) -> N otimes[R] M ->ₗ[R] P otimes[R] M) = rTensor M :=
  rfl

@[simp]
/--
theorem `lTensor_add` / 定理 `lTensor_add`

English:
theorem lTensor_add
  given: (f g : N ->ₗ[R] P)
  statement: (f + g).lTensor M = f.lTensor M + g.lTensor M
  proof: (lTensorHom M).map_add f g

@[simp]

中文:
定理 lTensor_add
  条件: (f g : N ->ₗ[R] P)
  结论: (f + g).lTensor M = f.lTensor M + g.lTensor M
  证明: (lTensorHom M).map_add f g

@[simp]

Depends on / 依赖: lTensorHom, map_add
-/
theorem lTensor_add (f g : N ->ₗ[R] P) : (f + g).lTensor M = f.lTensor M + g.lTensor M :=
  (lTensorHom M).map_add f g

@[simp]
/--
theorem `rTensor_add` / 定理 `rTensor_add`

English:
theorem rTensor_add
  given: (f g : N ->ₗ[R] P)
  statement: (f + g).rTensor M = f.rTensor M + g.rTensor M
  proof: (rTensorHom M).map_add f g

@[simp]

中文:
定理 rTensor_add
  条件: (f g : N ->ₗ[R] P)
  结论: (f + g).rTensor M = f.rTensor M + g.rTensor M
  证明: (rTensorHom M).map_add f g

@[simp]

Depends on / 依赖: map_add, rTensorHom
-/
theorem rTensor_add (f g : N ->ₗ[R] P) : (f + g).rTensor M = f.rTensor M + g.rTensor M :=
  (rTensorHom M).map_add f g

@[simp]
/--
theorem `lTensor_zero` / 定理 `lTensor_zero`

English:
theorem lTensor_zero
  statement: lTensor M (0 : N ->ₗ[R] P) = 0
  proof: (lTensorHom M).map_zero

@[simp]

中文:
定理 lTensor_zero
  结论: lTensor M (0 : N ->ₗ[R] P) = 0
  证明: (lTensorHom M).map_zero

@[simp]

Depends on / 依赖: lTensorHom, map_zero
-/
theorem lTensor_zero : lTensor M (0 : N ->ₗ[R] P) = 0 :=
  (lTensorHom M).map_zero

@[simp]
/--
theorem `rTensor_zero` / 定理 `rTensor_zero`

English:
theorem rTensor_zero
  statement: rTensor M (0 : N ->ₗ[R] P) = 0
  proof: (rTensorHom M).map_zero

@[simp]

中文:
定理 rTensor_zero
  结论: rTensor M (0 : N ->ₗ[R] P) = 0
  证明: (rTensorHom M).map_zero

@[simp]

Depends on / 依赖: map_zero, rTensorHom
-/
theorem rTensor_zero : rTensor M (0 : N ->ₗ[R] P) = 0 :=
  (rTensorHom M).map_zero

@[simp]
/--
theorem `lTensor_smul` / 定理 `lTensor_smul`

English:
theorem lTensor_smul
  given: (r : R) (f : N ->ₗ[R] P)
  statement: (r • f).lTensor M = r • f.lTensor M
  proof: (lTensorHom M).map_smul r f

@[simp]

中文:
定理 lTensor_smul
  条件: (r : R) (f : N ->ₗ[R] P)
  结论: (r • f).lTensor M = r • f.lTensor M
  证明: (lTensorHom M).map_smul r f

@[simp]

Depends on / 依赖: lTensorHom, map_smul
-/
theorem lTensor_smul (r : R) (f : N ->ₗ[R] P) : (r • f).lTensor M = r • f.lTensor M :=
  (lTensorHom M).map_smul r f

@[simp]
/--
theorem `rTensor_smul` / 定理 `rTensor_smul`

English:
theorem rTensor_smul
  given: (r : R) (f : N ->ₗ[R] P)
  statement: (r • f).rTensor M = r • f.rTensor M
  proof: (rTensorHom M).map_smul r f

中文:
定理 rTensor_smul
  条件: (r : R) (f : N ->ₗ[R] P)
  结论: (r • f).rTensor M = r • f.rTensor M
  证明: (rTensorHom M).map_smul r f

Depends on / 依赖: map_smul, rTensorHom
-/
theorem rTensor_smul (r : R) (f : N ->ₗ[R] P) : (r • f).rTensor M = r • f.rTensor M :=
  (rTensorHom M).map_smul r f

/--
theorem `lTensor_comp` / 定理 `lTensor_comp`

English:
theorem lTensor_comp
  statement: (g.comp f).lTensor M = (g.lTensor M).comp (f.lTensor M)
  proof: by
  ext m n
  simp only [compr₂ₛₗ_apply, mk_apply, comp_apply, lTensor_tmul]

中文:
定理 lTensor_comp
  结论: (g.comp f).lTensor M = (g.lTensor M).comp (f.lTensor M)
  证明: by
  ext m n
  simp only [compr₂ₛₗ_apply, mk_apply, comp_apply, lTensor_tmul]

Depends on / 依赖: comp_apply, lTensor_tmul, mk_apply
-/
theorem lTensor_comp : (g.comp f).lTensor M = (g.lTensor M).comp (f.lTensor M) := by
  ext m n
  simp only [compr₂ₛₗ_apply, mk_apply, comp_apply, lTensor_tmul]

/--
theorem `lTensor_comp_apply` / 定理 `lTensor_comp_apply`

English:
theorem lTensor_comp_apply
  given: (x : M otimes[R] N)
  proof: by rw [lTensor_comp, coe_comp]; rfl

中文:
定理 lTensor_comp_apply
  条件: (x : M otimes[R] N)
  证明: by rw [lTensor_comp, coe_comp]; rfl

Depends on / 依赖: coe_comp, lTensor_comp
-/
theorem lTensor_comp_apply (x : M otimes[R] N) :
    (g.comp f).lTensor M x = (g.lTensor M) ((f.lTensor M) x) := by rw [lTensor_comp, coe_comp]; rfl

/--
theorem `rTensor_comp` / 定理 `rTensor_comp`

English:
theorem rTensor_comp
  statement: (g.comp f).rTensor M = (g.rTensor M).comp (f.rTensor M)
  proof: by
  ext m n
  simp only [compr₂ₛₗ_apply, mk_apply, comp_apply, rTensor_tmul]

中文:
定理 rTensor_comp
  结论: (g.comp f).rTensor M = (g.rTensor M).comp (f.rTensor M)
  证明: by
  ext m n
  simp only [compr₂ₛₗ_apply, mk_apply, comp_apply, rTensor_tmul]

Depends on / 依赖: comp_apply, mk_apply, rTensor_tmul
-/
theorem rTensor_comp : (g.comp f).rTensor M = (g.rTensor M).comp (f.rTensor M) := by
  ext m n
  simp only [compr₂ₛₗ_apply, mk_apply, comp_apply, rTensor_tmul]

/--
theorem `rTensor_comp_apply` / 定理 `rTensor_comp_apply`

English:
theorem rTensor_comp_apply
  given: (x : N otimes[R] M)
  proof: by rw [rTensor_comp, coe_comp]; rfl

中文:
定理 rTensor_comp_apply
  条件: (x : N otimes[R] M)
  证明: by rw [rTensor_comp, coe_comp]; rfl

Depends on / 依赖: coe_comp, rTensor_comp
-/
theorem rTensor_comp_apply (x : N otimes[R] M) :
    (g.comp f).rTensor M x = (g.rTensor M) ((f.rTensor M) x) := by rw [rTensor_comp, coe_comp]; rfl

/--
theorem `lTensor_mul` / 定理 `lTensor_mul`

English:
theorem lTensor_mul
  given: (f g : Module.End R N)
  statement: (f * g).lTensor M = f.lTensor M * g.lTensor M
  proof: lTensor_comp M f g

中文:
定理 lTensor_mul
  条件: (f g : 模.End R N)
  结论: (f * g).lTensor M = f.lTensor M * g.lTensor M
  证明: lTensor_comp M f g

Depends on / 依赖: lTensor_comp
-/
theorem lTensor_mul (f g : Module.End R N) : (f * g).lTensor M = f.lTensor M * g.lTensor M :=
  lTensor_comp M f g

/--
theorem `rTensor_mul` / 定理 `rTensor_mul`

English:
theorem rTensor_mul
  given: (f g : Module.End R N)
  statement: (f * g).rTensor M = f.rTensor M * g.rTensor M
  proof: rTensor_comp M f g

中文:
定理 rTensor_mul
  条件: (f g : 模.End R N)
  结论: (f * g).rTensor M = f.rTensor M * g.rTensor M
  证明: rTensor_comp M f g

Depends on / 依赖: rTensor_comp
-/
theorem rTensor_mul (f g : Module.End R N) : (f * g).rTensor M = f.rTensor M * g.rTensor M :=
  rTensor_comp M f g

variable (N)

@[simp]
/--
theorem `lTensor_id` / 定理 `lTensor_id`

English:
theorem lTensor_id
  statement: (id : N ->ₗ[R] N).lTensor M = id
  proof: map_id

中文:
定理 lTensor_id
  结论: (id : N ->ₗ[R] N).lTensor M = id
  证明: map_id

Depends on / 依赖: map_id
-/
theorem lTensor_id : (id : N ->ₗ[R] N).lTensor M = id :=
  map_id

-- `simp` can prove this.
/--
theorem `lTensor_id_apply` / 定理 `lTensor_id_apply`

English:
theorem lTensor_id_apply
  given: (x : M otimes[R] N)
  statement: (LinearMap.id : N ->ₗ[R] N).lTensor M x = x
  proof: by
  rw [lTensor_id]; rw [id_coe]; rw [_root_.id]

@[simp]

中文:
定理 lTensor_id_apply
  条件: (x : M otimes[R] N)
  结论: (线性映射.id : N ->ₗ[R] N).lTensor M x = x
  证明: by
  rw [lTensor_id]; rw [id_coe]; rw [_root_.id]

@[simp]

Depends on / 依赖: _root_, _root_.id, id_coe, lTensor_id
-/
theorem lTensor_id_apply (x : M otimes[R] N) : (LinearMap.id : N ->ₗ[R] N).lTensor M x = x := by
  rw [lTensor_id]; rw [id_coe]; rw [_root_.id]

@[simp]
/--
theorem `rTensor_id` / 定理 `rTensor_id`

English:
theorem rTensor_id
  statement: (id : N ->ₗ[R] N).rTensor M = id
  proof: map_id

中文:
定理 rTensor_id
  结论: (id : N ->ₗ[R] N).rTensor M = id
  证明: map_id

Depends on / 依赖: map_id
-/
theorem rTensor_id : (id : N ->ₗ[R] N).rTensor M = id :=
  map_id

-- `simp` can prove this.
/--
theorem `rTensor_id_apply` / 定理 `rTensor_id_apply`

English:
theorem rTensor_id_apply
  given: (x : N otimes[R] M)
  statement: (LinearMap.id : N ->ₗ[R] N).rTensor M x = x
  proof: by
  rw [rTensor_id]; rw [id_coe]; rw [_root_.id]

@[simp]

中文:
定理 rTensor_id_apply
  条件: (x : N otimes[R] M)
  结论: (线性映射.id : N ->ₗ[R] N).rTensor M x = x
  证明: by
  rw [rTensor_id]; rw [id_coe]; rw [_root_.id]

@[simp]

Depends on / 依赖: _root_, _root_.id, id_coe, rTensor_id
-/
theorem rTensor_id_apply (x : N otimes[R] M) : (LinearMap.id : N ->ₗ[R] N).rTensor M x = x := by
  rw [rTensor_id]; rw [id_coe]; rw [_root_.id]

@[simp]
/--
theorem `lTensor_smul_action` / 定理 `lTensor_smul_action`

English:
theorem lTensor_smul_action
  given: (r : R)
  proof: (lTensor_smul M r LinearMap.id).trans (congrArg _ (lTensor_id M N))

@[simp]

中文:
定理 lTensor_smul_action
  条件: (r : R)
  证明: (lTensor_smul M r LinearMap.id).trans (congrArg _ (lTensor_id M N))

@[simp]

Depends on / 依赖: LinearMap, LinearMap.id, lTensor_id, lTensor_smul
-/
theorem lTensor_smul_action (r : R) :
    (DistribSMul.toLinearMap R N r).lTensor M =
      DistribSMul.toLinearMap R (M otimes[R] N) r :=
  (lTensor_smul M r LinearMap.id).trans (congrArg _ (lTensor_id M N))

@[simp]
/--
theorem `rTensor_smul_action` / 定理 `rTensor_smul_action`

English:
theorem rTensor_smul_action
  given: (r : R)
  proof: (rTensor_smul M r LinearMap.id).trans (congrArg _ (rTensor_id M N))

中文:
定理 rTensor_smul_action
  条件: (r : R)
  证明: (rTensor_smul M r LinearMap.id).trans (congrArg _ (rTensor_id M N))

Depends on / 依赖: LinearMap, LinearMap.id, rTensor_id, rTensor_smul
-/
theorem rTensor_smul_action (r : R) :
    (DistribSMul.toLinearMap R N r).rTensor M =
      DistribSMul.toLinearMap R (N otimes[R] M) r :=
  (rTensor_smul M r LinearMap.id).trans (congrArg _ (rTensor_id M N))

variable {N}

@[simp]
/--
theorem `lTensor_comp_rTensor` / 定理 `lTensor_comp_rTensor`

English:
theorem lTensor_comp_rTensor
  given: (f : M ->ₗ[R] P) (g : N ->ₗ[R] Q)
  proof: by
  simp only [lTensor, rTensor, ← map_comp, id_comp, comp_id]

@[simp]

中文:
定理 lTensor_comp_rTensor
  条件: (f : M ->ₗ[R] P) (g : N ->ₗ[R] Q)
  证明: by
  simp only [lTensor, rTensor, ← map_comp, id_comp, comp_id]

@[simp]

Depends on / 依赖: comp_id, id_comp, lTensor, map_comp, rTensor
-/
theorem lTensor_comp_rTensor (f : M ->ₗ[R] P) (g : N ->ₗ[R] Q) :
    (g.lTensor P).comp (f.rTensor N) = map f g := by
  simp only [lTensor, rTensor, ← map_comp, id_comp, comp_id]

@[simp]
/--
theorem `rTensor_comp_lTensor` / 定理 `rTensor_comp_lTensor`

English:
theorem rTensor_comp_lTensor
  given: (f : M ->ₗ[R] P) (g : N ->ₗ[R] Q)
  proof: by
  simp only [lTensor, rTensor, ← map_comp, id_comp, comp_id]

@[simp]

中文:
定理 rTensor_comp_lTensor
  条件: (f : M ->ₗ[R] P) (g : N ->ₗ[R] Q)
  证明: by
  simp only [lTensor, rTensor, ← map_comp, id_comp, comp_id]

@[simp]

Depends on / 依赖: comp_id, id_comp, lTensor, map_comp, rTensor
-/
theorem rTensor_comp_lTensor (f : M ->ₗ[R] P) (g : N ->ₗ[R] Q) :
    (f.rTensor Q).comp (g.lTensor M) = map f g := by
  simp only [lTensor, rTensor, ← map_comp, id_comp, comp_id]

@[simp]
/--
theorem `map_comp_rTensor` / 定理 `map_comp_rTensor`

English:
theorem map_comp_rTensor
  given: (f : M ->ₗ[R] P) (g : N ->ₗ[R] Q) (f' : S ->ₗ[R] M)
  proof: by
  simp only [rTensor, ← map_comp, comp_id]

@[simp]

中文:
定理 map_comp_rTensor
  条件: (f : M ->ₗ[R] P) (g : N ->ₗ[R] Q) (f' : S ->ₗ[R] M)
  证明: by
  simp only [rTensor, ← map_comp, comp_id]

@[simp]

Depends on / 依赖: comp_id, map_comp, rTensor
-/
theorem map_comp_rTensor (f : M ->ₗ[R] P) (g : N ->ₗ[R] Q) (f' : S ->ₗ[R] M) :
    (map f g).comp (f'.rTensor _) = map (f.comp f') g := by
  simp only [rTensor, ← map_comp, comp_id]

@[simp]
/--
theorem `map_rTensor` / 定理 `map_rTensor`

English:
theorem map_rTensor
  given: (f : M ->ₗ[R] P) (g : N ->ₗ[R] Q) (f' : S ->ₗ[R] M) (x : S otimes[R] N)
  proof: LinearMap.congr_fun (map_comp_rTensor _ _ _ _) x

@[simp]

中文:
定理 map_rTensor
  条件: (f : M ->ₗ[R] P) (g : N ->ₗ[R] Q) (f' : S ->ₗ[R] M) (x : S otimes[R] N)
  证明: LinearMap.congr_fun (map_comp_rTensor _ _ _ _) x

@[simp]

Depends on / 依赖: LinearMap, LinearMap.congr_fun, congr_fun, map_comp_rTensor
-/
theorem map_rTensor (f : M ->ₗ[R] P) (g : N ->ₗ[R] Q) (f' : S ->ₗ[R] M) (x : S otimes[R] N) :
    map f g (f'.rTensor _ x) = map (f.comp f') g x :=
  LinearMap.congr_fun (map_comp_rTensor _ _ _ _) x

@[simp]
/--
theorem `map_comp_lTensor` / 定理 `map_comp_lTensor`

English:
theorem map_comp_lTensor
  given: (f : M ->ₗ[R] P) (g : N ->ₗ[R] Q) (g' : S ->ₗ[R] N)
  proof: by
  simp only [lTensor, ← map_comp, comp_id]

@[simp]

中文:
定理 map_comp_lTensor
  条件: (f : M ->ₗ[R] P) (g : N ->ₗ[R] Q) (g' : S ->ₗ[R] N)
  证明: by
  simp only [lTensor, ← map_comp, comp_id]

@[simp]

Depends on / 依赖: comp_id, lTensor, map_comp
-/
theorem map_comp_lTensor (f : M ->ₗ[R] P) (g : N ->ₗ[R] Q) (g' : S ->ₗ[R] N) :
    (map f g).comp (g'.lTensor _) = map f (g.comp g') := by
  simp only [lTensor, ← map_comp, comp_id]

@[simp]
/--
lemma `map_lTensor` / 引理 `map_lTensor`

English:
lemma map_lTensor
  given: (f : M ->ₗ[R] P) (g : N ->ₗ[R] Q) (g' : S ->ₗ[R] N) (x : M otimes[R] S)
  proof: LinearMap.congr_fun (map_comp_lTensor _ _ _ _) x

@[simp]

中文:
引理 map_lTensor
  条件: (f : M ->ₗ[R] P) (g : N ->ₗ[R] Q) (g' : S ->ₗ[R] N) (x : M otimes[R] S)
  证明: LinearMap.congr_fun (map_comp_lTensor _ _ _ _) x

@[simp]

Depends on / 依赖: LinearMap, LinearMap.congr_fun, congr_fun, map_comp_lTensor
-/
lemma map_lTensor (f : M ->ₗ[R] P) (g : N ->ₗ[R] Q) (g' : S ->ₗ[R] N) (x : M otimes[R] S) :
    map f g (g'.lTensor M x) = map f (g ∘ₗ g') x :=
  LinearMap.congr_fun (map_comp_lTensor _ _ _ _) x

@[simp]
/--
theorem `rTensor_comp_map` / 定理 `rTensor_comp_map`

English:
theorem rTensor_comp_map
  given: (f' : P ->ₗ[R] S) (f : M ->ₗ[R] P) (g : N ->ₗ[R] Q)
  proof: by
  simp only [rTensor, ← map_comp, id_comp]

@[simp]

中文:
定理 rTensor_comp_map
  条件: (f' : P ->ₗ[R] S) (f : M ->ₗ[R] P) (g : N ->ₗ[R] Q)
  证明: by
  simp only [rTensor, ← map_comp, id_comp]

@[simp]

Depends on / 依赖: id_comp, map_comp, rTensor
-/
theorem rTensor_comp_map (f' : P ->ₗ[R] S) (f : M ->ₗ[R] P) (g : N ->ₗ[R] Q) :
    (f'.rTensor _).comp (map f g) = map (f'.comp f) g := by
  simp only [rTensor, ← map_comp, id_comp]

@[simp]
/--
lemma `rTensor_map` / 引理 `rTensor_map`

English:
lemma rTensor_map
  given: (f' : P ->ₗ[R] S) (f : M ->ₗ[R] P) (g : N ->ₗ[R] Q) (x : M otimes[R] N)
  proof: LinearMap.congr_fun (rTensor_comp_map _ _ f g) x

@[simp]

中文:
引理 rTensor_map
  条件: (f' : P ->ₗ[R] S) (f : M ->ₗ[R] P) (g : N ->ₗ[R] Q) (x : M otimes[R] N)
  证明: LinearMap.congr_fun (rTensor_comp_map _ _ f g) x

@[simp]

Depends on / 依赖: LinearMap, LinearMap.congr_fun, congr_fun, rTensor_comp_map
-/
lemma rTensor_map (f' : P ->ₗ[R] S) (f : M ->ₗ[R] P) (g : N ->ₗ[R] Q) (x : M otimes[R] N) :
    f'.rTensor Q (map f g x) = map (f' ∘ₗ f) g x :=
  LinearMap.congr_fun (rTensor_comp_map _ _ f g) x

@[simp]
/--
theorem `lTensor_comp_map` / 定理 `lTensor_comp_map`

English:
theorem lTensor_comp_map
  given: (g' : Q ->ₗ[R] S) (f : M ->ₗ[R] P) (g : N ->ₗ[R] Q)
  proof: by
  simp only [lTensor, ← map_comp, id_comp]

@[simp]

中文:
定理 lTensor_comp_map
  条件: (g' : Q ->ₗ[R] S) (f : M ->ₗ[R] P) (g : N ->ₗ[R] Q)
  证明: by
  simp only [lTensor, ← map_comp, id_comp]

@[simp]

Depends on / 依赖: id_comp, lTensor, map_comp
-/
theorem lTensor_comp_map (g' : Q ->ₗ[R] S) (f : M ->ₗ[R] P) (g : N ->ₗ[R] Q) :
    (g'.lTensor _).comp (map f g) = map f (g'.comp g) := by
  simp only [lTensor, ← map_comp, id_comp]

@[simp]
/--
lemma `lTensor_map` / 引理 `lTensor_map`

English:
lemma lTensor_map
  given: (g' : Q ->ₗ[R] S) (f : M ->ₗ[R] P) (g : N ->ₗ[R] Q) (x : M otimes[R] N)
  proof: LinearMap.congr_fun (lTensor_comp_map _ _ f g) x

中文:
引理 lTensor_map
  条件: (g' : Q ->ₗ[R] S) (f : M ->ₗ[R] P) (g : N ->ₗ[R] Q) (x : M otimes[R] N)
  证明: LinearMap.congr_fun (lTensor_comp_map _ _ f g) x

Depends on / 依赖: LinearMap, LinearMap.congr_fun, congr_fun, lTensor_comp_map
-/
lemma lTensor_map (g' : Q ->ₗ[R] S) (f : M ->ₗ[R] P) (g : N ->ₗ[R] Q) (x : M otimes[R] N) :
    g'.lTensor P (map f g x) = map f (g' ∘ₗ g) x :=
  LinearMap.congr_fun (lTensor_comp_map _ _ f g) x

variable {M}

/--
theorem `lTensor_comp_comm` / 定理 `lTensor_comp_comm`

English:
theorem lTensor_comp_comm
  given: (f : M ->ₗ[R] P)
  proof: TensorProduct.map_comp_comm_eq _ _

中文:
定理 lTensor_comp_comm
  条件: (f : M ->ₗ[R] P)
  证明: TensorProduct.map_comp_comm_eq _ _

Depends on / 依赖: TensorProduct, TensorProduct.map_comp_comm_eq, map_comp_comm_eq
-/
theorem lTensor_comp_comm (f : M ->ₗ[R] P) :
    lTensor N f ∘ₗ TensorProduct.comm R M N = TensorProduct.comm R P N ∘ₗ rTensor N f :=
  TensorProduct.map_comp_comm_eq _ _

/--
theorem `rTensor_comp_comm` / 定理 `rTensor_comp_comm`

English:
theorem rTensor_comp_comm
  given: (f : M ->ₗ[R] P)
  proof: TensorProduct.map_comp_comm_eq _ _

中文:
定理 rTensor_comp_comm
  条件: (f : M ->ₗ[R] P)
  证明: TensorProduct.map_comp_comm_eq _ _

Depends on / 依赖: TensorProduct, TensorProduct.map_comp_comm_eq, map_comp_comm_eq
-/
theorem rTensor_comp_comm (f : M ->ₗ[R] P) :
    rTensor N f ∘ₗ TensorProduct.comm R N M = TensorProduct.comm R N P ∘ₗ lTensor N f :=
  TensorProduct.map_comp_comm_eq _ _

/--
theorem `lTensor_comm` / 定理 `lTensor_comm`

English:
theorem lTensor_comm
  given: (f : M ->ₗ[R] P) (x : M otimes[R] N)
  proof: congr($(LinearMap.lTensor_comp_comm f) _)

中文:
定理 lTensor_comm
  条件: (f : M ->ₗ[R] P) (x : M otimes[R] N)
  证明: congr($(LinearMap.lTensor_comp_comm f) _)

Depends on / 依赖: LinearMap, LinearMap.lTensor_comp_comm, lTensor_comp_comm
-/
theorem lTensor_comm (f : M ->ₗ[R] P) (x : M otimes[R] N) :
    lTensor N f (TensorProduct.comm R M N x) = TensorProduct.comm R P N (rTensor N f x) :=
  congr($(LinearMap.lTensor_comp_comm f) _)

/--
theorem `rTensor_comm` / 定理 `rTensor_comm`

English:
theorem rTensor_comm
  given: (f : M ->ₗ[R] P) (x : N otimes[R] M)
  proof: congr($(LinearMap.rTensor_comp_comm f) _)

@[simp]

中文:
定理 rTensor_comm
  条件: (f : M ->ₗ[R] P) (x : N otimes[R] M)
  证明: congr($(LinearMap.rTensor_comp_comm f) _)

@[simp]

Depends on / 依赖: LinearMap, LinearMap.rTensor_comp_comm, rTensor_comp_comm
-/
theorem rTensor_comm (f : M ->ₗ[R] P) (x : N otimes[R] M) :
    rTensor N f (TensorProduct.comm R N M x) = TensorProduct.comm R N P (lTensor N f x) :=
  congr($(LinearMap.rTensor_comp_comm f) _)

@[simp]
/--
theorem `rTensor_pow` / 定理 `rTensor_pow`

English:
theorem rTensor_pow
  given: (f : M ->ₗ[R] M) (n : Nat)
  statement: f.rTensor N ^ n = (f ^ n).rTensor N
  proof: by
  have h := TensorProduct.map_pow f (id : N ->ₗ[R] N) n
  rwa [Module.End.id_pow] at h

@[simp]

中文:
定理 rTensor_pow
  条件: (f : M ->ₗ[R] M) (n : 自然数)
  结论: f.rTensor N ^ n = (f ^ n).rTensor N
  证明: by
  have h := TensorProduct.map_pow f (id : N ->ₗ[R] N) n
  rwa [Module.End.id_pow] at h

@[simp]

Depends on / 依赖: Module, Module.End.id_pow, TensorProduct, TensorProduct.map_pow, id_pow, map_pow
-/
theorem rTensor_pow (f : M ->ₗ[R] M) (n : Nat) : f.rTensor N ^ n = (f ^ n).rTensor N := by
  have h := TensorProduct.map_pow f (id : N ->ₗ[R] N) n
  rwa [Module.End.id_pow] at h

@[simp]
/--
theorem `lTensor_pow` / 定理 `lTensor_pow`

English:
theorem lTensor_pow
  given: (f : N ->ₗ[R] N) (n : Nat)
  statement: f.lTensor M ^ n = (f ^ n).lTensor M
  proof: by
  have h := TensorProduct.map_pow (id : M ->ₗ[R] M) f n
  rwa [Module.End.id_pow] at h

中文:
定理 lTensor_pow
  条件: (f : N ->ₗ[R] N) (n : 自然数)
  结论: f.lTensor M ^ n = (f ^ n).lTensor M
  证明: by
  have h := TensorProduct.map_pow (id : M ->ₗ[R] M) f n
  rwa [Module.End.id_pow] at h

Depends on / 依赖: Module, Module.End.id_pow, TensorProduct, TensorProduct.map_pow, id_pow, map_pow
-/
theorem lTensor_pow (f : N ->ₗ[R] N) (n : Nat) : f.lTensor M ^ n = (f ^ n).lTensor M := by
  have h := TensorProduct.map_pow (id : M ->ₗ[R] M) f n
  rwa [Module.End.id_pow] at h

end LinearMap

namespace LinearEquiv

variable {N}

/--
Definition of `lTensor` / `lTensor` 的定义

English:
definition lTensor
  signature: (f : N ≃ₗ[R] P)
  body: TensorProduct.congr (refl R M) f

中文:
定义 lTensor
  签名: (f : N ≃ₗ[R] P)
  定义体: TensorProduct.congr (refl R M) f

Depends on / 依赖: TensorProduct, TensorProduct.congr
-/
def lTensor (f : N ≃ₗ[R] P) : M otimes[R] N ≃ₗ[R] M otimes[R] P := TensorProduct.congr (refl R M) f

/--
Definition of `rTensor` / `rTensor` 的定义

English:
definition rTensor
  signature: (f : N ≃ₗ[R] P)
  body: TensorProduct.congr f (refl R M)

中文:
定义 rTensor
  签名: (f : N ≃ₗ[R] P)
  定义体: TensorProduct.congr f (refl R M)

Depends on / 依赖: TensorProduct, TensorProduct.congr
-/
def rTensor (f : N ≃ₗ[R] P) : N otimes[R] M ≃ₗ[R] P otimes[R] M := TensorProduct.congr f (refl R M)

variable (g : P ≃ₗ[R] Q) (f : N ≃ₗ[R] P) (m : M) (n : N) (p : P) (x : M otimes[R] N) (y : N otimes[R] M)

/--
theorem `symm_lTensor` / 定理 `symm_lTensor`

English:
theorem symm_lTensor
  statement: (f.lTensor M).symm = f.symm.lTensor M
  proof: rfl

中文:
定理 symm_lTensor
  结论: (f.lTensor M).symm = f.symm.lTensor M
  证明: rfl
-/
@[simp] theorem symm_lTensor : (f.lTensor M).symm = f.symm.lTensor M := rfl

/--
theorem `symm_rTensor` / 定理 `symm_rTensor`

English:
theorem symm_rTensor
  statement: (f.rTensor M).symm = f.symm.rTensor M
  proof: rfl

中文:
定理 symm_rTensor
  结论: (f.rTensor M).symm = f.symm.rTensor M
  证明: rfl
-/
@[simp] theorem symm_rTensor : (f.rTensor M).symm = f.symm.rTensor M := rfl

/--
theorem `coe_lTensor` / 定理 `coe_lTensor`

English:
theorem coe_lTensor
  statement: lTensor M f = (f : N ->ₗ[R] P).lTensor M
  proof: rfl

@[deprecated "use symm_lTensor and coe_lTensor" (since := "2026-07-04")]

中文:
定理 coe_lTensor
  结论: lTensor M f = (f : N ->ₗ[R] P).lTensor M
  证明: rfl

@[deprecated "use symm_lTensor and coe_lTensor" (since := "2026-07-04")]
-/
@[simp] theorem coe_lTensor : lTensor M f = (f : N ->ₗ[R] P).lTensor M := rfl

@[deprecated "use symm_lTensor and coe_lTensor" (since := "2026-07-04")]
/--
theorem `coe_lTensor_symm` / 定理 `coe_lTensor_symm`

English:
theorem coe_lTensor_symm
  statement: (lTensor M f).symm = (f.symm : P ->ₗ[R] N).lTensor M
  proof: rfl

中文:
定理 coe_lTensor_symm
  结论: (lTensor M f).symm = (f.symm : P ->ₗ[R] N).lTensor M
  证明: rfl
-/
theorem coe_lTensor_symm : (lTensor M f).symm = (f.symm : P ->ₗ[R] N).lTensor M := rfl

/--
theorem `coe_rTensor` / 定理 `coe_rTensor`

English:
theorem coe_rTensor
  statement: rTensor M f = (f : N ->ₗ[R] P).rTensor M
  proof: rfl

@[deprecated "use symm_rTensor and coe_rTensor" (since := "2026-07-04")]

中文:
定理 coe_rTensor
  结论: rTensor M f = (f : N ->ₗ[R] P).rTensor M
  证明: rfl

@[deprecated "use symm_rTensor and coe_rTensor" (since := "2026-07-04")]
-/
@[simp] theorem coe_rTensor : rTensor M f = (f : N ->ₗ[R] P).rTensor M := rfl

@[deprecated "use symm_rTensor and coe_rTensor" (since := "2026-07-04")]
/--
theorem `coe_rTensor_symm` / 定理 `coe_rTensor_symm`

English:
theorem coe_rTensor_symm
  statement: (rTensor M f).symm = (f.symm : P ->ₗ[R] N).rTensor M
  proof: rfl

中文:
定理 coe_rTensor_symm
  结论: (rTensor M f).symm = (f.symm : P ->ₗ[R] N).rTensor M
  证明: rfl
-/
theorem coe_rTensor_symm : (rTensor M f).symm = (f.symm : P ->ₗ[R] N).rTensor M := rfl

/--
theorem `lTensor_tmul` / 定理 `lTensor_tmul`

English:
theorem lTensor_tmul
  statement: f.lTensor M (m otimesₜ n) = m otimesₜ f n
  proof: rfl

@[deprecated "use symm_lTensor and lTensor_tmul" (since := "2026-07-04")]

中文:
定理 lTensor_tmul
  结论: f.lTensor M (m otimesₜ n) = m otimesₜ f n
  证明: rfl

@[deprecated "use symm_lTensor and lTensor_tmul" (since := "2026-07-04")]
-/
@[simp] theorem lTensor_tmul : f.lTensor M (m otimesₜ n) = m otimesₜ f n := rfl

@[deprecated "use symm_lTensor and lTensor_tmul" (since := "2026-07-04")]
/--
theorem `lTensor_symm_tmul` / 定理 `lTensor_symm_tmul`

English:
theorem lTensor_symm_tmul
  statement: (f.lTensor M).symm (m otimesₜ p) = m otimesₜ f.symm p
  proof: rfl

中文:
定理 lTensor_symm_tmul
  结论: (f.lTensor M).symm (m otimesₜ p) = m otimesₜ f.symm p
  证明: rfl
-/
theorem lTensor_symm_tmul : (f.lTensor M).symm (m otimesₜ p) = m otimesₜ f.symm p := rfl

/--
theorem `rTensor_tmul` / 定理 `rTensor_tmul`

English:
theorem rTensor_tmul
  statement: f.rTensor M (n otimesₜ m) = f n otimesₜ m
  proof: rfl

@[deprecated "use symm_rTensor and rTensor_tmul" (since := "2026-07-04")]

中文:
定理 rTensor_tmul
  结论: f.rTensor M (n otimesₜ m) = f n otimesₜ m
  证明: rfl

@[deprecated "use symm_rTensor and rTensor_tmul" (since := "2026-07-04")]
-/
@[simp] theorem rTensor_tmul : f.rTensor M (n otimesₜ m) = f n otimesₜ m := rfl

@[deprecated "use symm_rTensor and rTensor_tmul" (since := "2026-07-04")]
/--
theorem `rTensor_symm_tmul` / 定理 `rTensor_symm_tmul`

English:
theorem rTensor_symm_tmul
  statement: (f.rTensor M).symm (p otimesₜ m) = f.symm p otimesₜ m
  proof: rfl

中文:
定理 rTensor_symm_tmul
  结论: (f.rTensor M).symm (p otimesₜ m) = f.symm p otimesₜ m
  证明: rfl
-/
theorem rTensor_symm_tmul : (f.rTensor M).symm (p otimesₜ m) = f.symm p otimesₜ m := rfl

/--
lemma `comm_trans_rTensor_trans_comm_eq` / 引理 `comm_trans_rTensor_trans_comm_eq`

English:
lemma comm_trans_rTensor_trans_comm_eq
  given: (g : N ≃ₗ[R] P)
  proof: toLinearMap_injective TensorProduct.ext rfl

中文:
引理 comm_trans_rTensor_trans_comm_eq
  条件: (g : N ≃ₗ[R] P)
  证明: toLinearMap_injective TensorProduct.ext rfl

Depends on / 依赖: TensorProduct, TensorProduct.ext, toLinearMap_injective
-/
lemma comm_trans_rTensor_trans_comm_eq (g : N ≃ₗ[R] P) :
    TensorProduct.comm R Q N ≪≫ₗ rTensor Q g ≪≫ₗ TensorProduct.comm R P Q = lTensor Q g :=
toLinearMap_injective TensorProduct.ext rfl

/--
lemma `comm_trans_lTensor_trans_comm_eq` / 引理 `comm_trans_lTensor_trans_comm_eq`

English:
lemma comm_trans_lTensor_trans_comm_eq
  given: (g : N ≃ₗ[R] P)
  proof: toLinearMap_injective TensorProduct.ext rfl

中文:
引理 comm_trans_lTensor_trans_comm_eq
  条件: (g : N ≃ₗ[R] P)
  证明: toLinearMap_injective TensorProduct.ext rfl

Depends on / 依赖: TensorProduct, TensorProduct.ext, toLinearMap_injective
-/
lemma comm_trans_lTensor_trans_comm_eq (g : N ≃ₗ[R] P) :
    TensorProduct.comm R N Q ≪≫ₗ lTensor Q g ≪≫ₗ TensorProduct.comm R Q P = rTensor Q g :=
toLinearMap_injective TensorProduct.ext rfl

/--
theorem `lTensor_trans` / 定理 `lTensor_trans`

English:
theorem lTensor_trans
  statement: (f ≪≫ₗ g).lTensor M = f.lTensor M ≪≫ₗ g.lTensor M
  proof: toLinearMap_injective LinearMap.lTensor_comp M _ _

中文:
定理 lTensor_trans
  结论: (f ≪≫ₗ g).lTensor M = f.lTensor M ≪≫ₗ g.lTensor M
  证明: toLinearMap_injective LinearMap.lTensor_comp M _ _

Depends on / 依赖: LinearMap, LinearMap.lTensor_comp, lTensor_comp, toLinearMap_injective
-/
theorem lTensor_trans : (f ≪≫ₗ g).lTensor M = f.lTensor M ≪≫ₗ g.lTensor M :=
toLinearMap_injective LinearMap.lTensor_comp M _ _

/--
theorem `lTensor_trans_apply` / 定理 `lTensor_trans_apply`

English:
theorem lTensor_trans_apply
  statement: (f ≪≫ₗ g).lTensor M x = g.lTensor M (f.lTensor M x)
  proof: LinearMap.lTensor_comp_apply M _ _ x

中文:
定理 lTensor_trans_apply
  结论: (f ≪≫ₗ g).lTensor M x = g.lTensor M (f.lTensor M x)
  证明: LinearMap.lTensor_comp_apply M _ _ x

Depends on / 依赖: LinearMap, LinearMap.lTensor_comp_apply, lTensor_comp_apply
-/
theorem lTensor_trans_apply : (f ≪≫ₗ g).lTensor M x = g.lTensor M (f.lTensor M x) :=
  LinearMap.lTensor_comp_apply M _ _ x

/--
theorem `rTensor_trans` / 定理 `rTensor_trans`

English:
theorem rTensor_trans
  statement: (f ≪≫ₗ g).rTensor M = f.rTensor M ≪≫ₗ g.rTensor M
  proof: toLinearMap_injective LinearMap.rTensor_comp M _ _

中文:
定理 rTensor_trans
  结论: (f ≪≫ₗ g).rTensor M = f.rTensor M ≪≫ₗ g.rTensor M
  证明: toLinearMap_injective LinearMap.rTensor_comp M _ _

Depends on / 依赖: LinearMap, LinearMap.rTensor_comp, rTensor_comp, toLinearMap_injective
-/
theorem rTensor_trans : (f ≪≫ₗ g).rTensor M = f.rTensor M ≪≫ₗ g.rTensor M :=
toLinearMap_injective LinearMap.rTensor_comp M _ _

/--
theorem `rTensor_trans_apply` / 定理 `rTensor_trans_apply`

English:
theorem rTensor_trans_apply
  statement: (f ≪≫ₗ g).rTensor M y = g.rTensor M (f.rTensor M y)
  proof: LinearMap.rTensor_comp_apply M _ _ y

中文:
定理 rTensor_trans_apply
  结论: (f ≪≫ₗ g).rTensor M y = g.rTensor M (f.rTensor M y)
  证明: LinearMap.rTensor_comp_apply M _ _ y

Depends on / 依赖: LinearMap, LinearMap.rTensor_comp_apply, rTensor_comp_apply
-/
theorem rTensor_trans_apply : (f ≪≫ₗ g).rTensor M y = g.rTensor M (f.rTensor M y) :=
  LinearMap.rTensor_comp_apply M _ _ y

/--
theorem `lTensor_mul` / 定理 `lTensor_mul`

English:
theorem lTensor_mul
  given: (f g : N ≃ₗ[R] N)
  statement: (f * g).lTensor M = f.lTensor M * g.lTensor M
  proof: lTensor_trans M f g

中文:
定理 lTensor_mul
  条件: (f g : N ≃ₗ[R] N)
  结论: (f * g).lTensor M = f.lTensor M * g.lTensor M
  证明: lTensor_trans M f g

Depends on / 依赖: lTensor_trans
-/
theorem lTensor_mul (f g : N ≃ₗ[R] N) : (f * g).lTensor M = f.lTensor M * g.lTensor M :=
  lTensor_trans M f g

/--
theorem `rTensor_mul` / 定理 `rTensor_mul`

English:
theorem rTensor_mul
  given: (f g : N ≃ₗ[R] N)
  statement: (f * g).rTensor M = f.rTensor M * g.rTensor M
  proof: rTensor_trans M f g

中文:
定理 rTensor_mul
  条件: (f g : N ≃ₗ[R] N)
  结论: (f * g).rTensor M = f.rTensor M * g.rTensor M
  证明: rTensor_trans M f g

Depends on / 依赖: rTensor_trans
-/
theorem rTensor_mul (f g : N ≃ₗ[R] N) : (f * g).rTensor M = f.rTensor M * g.rTensor M :=
  rTensor_trans M f g

variable (N)

/--
theorem `lTensor_refl` / 定理 `lTensor_refl`

English:
theorem lTensor_refl
  statement: (refl R N).lTensor M = refl R _
  proof: TensorProduct.congr_refl_refl

中文:
定理 lTensor_refl
  结论: (refl R N).lTensor M = refl R _
  证明: TensorProduct.congr_refl_refl
-/
@[simp] theorem lTensor_refl : (refl R N).lTensor M = refl R _ := TensorProduct.congr_refl_refl

/--
theorem `lTensor_refl_apply` / 定理 `lTensor_refl_apply`

English:
theorem lTensor_refl_apply
  statement: (refl R N).lTensor M x = x
  proof: by rw [lTensor_refl, refl_apply]

中文:
定理 lTensor_refl_apply
  结论: (refl R N).lTensor M x = x
  证明: by rw [lTensor_refl, refl_apply]

Depends on / 依赖: lTensor_refl, refl_apply
-/
theorem lTensor_refl_apply : (refl R N).lTensor M x = x := by rw [lTensor_refl, refl_apply]

/--
theorem `rTensor_refl` / 定理 `rTensor_refl`

English:
theorem rTensor_refl
  statement: (refl R N).rTensor M = refl R _
  proof: TensorProduct.congr_refl_refl

中文:
定理 rTensor_refl
  结论: (refl R N).rTensor M = refl R _
  证明: TensorProduct.congr_refl_refl
-/
@[simp] theorem rTensor_refl : (refl R N).rTensor M = refl R _ := TensorProduct.congr_refl_refl

/--
theorem `rTensor_refl_apply` / 定理 `rTensor_refl_apply`

English:
theorem rTensor_refl_apply
  statement: (refl R N).rTensor M y = y
  proof: by rw [rTensor_refl, refl_apply]

中文:
定理 rTensor_refl_apply
  结论: (refl R N).rTensor M y = y
  证明: by rw [rTensor_refl, refl_apply]

Depends on / 依赖: rTensor_refl, refl_apply
-/
theorem rTensor_refl_apply : (refl R N).rTensor M y = y := by rw [rTensor_refl, refl_apply]

variable {N}

/--
theorem `rTensor_trans_lTensor` / 定理 `rTensor_trans_lTensor`

English:
theorem rTensor_trans_lTensor
  given: (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q)
  proof: toLinearMap_injective LinearMap.lTensor_comp_rTensor M _ _

中文:
定理 rTensor_trans_lTensor
  条件: (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q)
  证明: toLinearMap_injective LinearMap.lTensor_comp_rTensor M _ _
-/
@[simp] theorem rTensor_trans_lTensor (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) :
    f.rTensor N ≪≫ₗ g.lTensor P = TensorProduct.congr f g :=
toLinearMap_injective LinearMap.lTensor_comp_rTensor M _ _

/--
theorem `lTensor_trans_rTensor` / 定理 `lTensor_trans_rTensor`

English:
theorem lTensor_trans_rTensor
  given: (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q)
  proof: toLinearMap_injective LinearMap.rTensor_comp_lTensor M _ _

中文:
定理 lTensor_trans_rTensor
  条件: (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q)
  证明: toLinearMap_injective LinearMap.rTensor_comp_lTensor M _ _
-/
@[simp] theorem lTensor_trans_rTensor (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) :
    g.lTensor M ≪≫ₗ f.rTensor Q = TensorProduct.congr f g :=
toLinearMap_injective LinearMap.rTensor_comp_lTensor M _ _

/--
theorem `rTensor_trans_congr` / 定理 `rTensor_trans_congr`

English:
theorem rTensor_trans_congr
  given: (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) (f' : S ≃ₗ[R] M)
  proof: toLinearMap_injective LinearMap.map_comp_rTensor M _ _ _

中文:
定理 rTensor_trans_congr
  条件: (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) (f' : S ≃ₗ[R] M)
  证明: toLinearMap_injective LinearMap.map_comp_rTensor M _ _ _
-/
@[simp] theorem rTensor_trans_congr (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) (f' : S ≃ₗ[R] M) :
    f'.rTensor _ ≪≫ₗ TensorProduct.congr f g = TensorProduct.congr (f' ≪≫ₗ f) g :=
toLinearMap_injective LinearMap.map_comp_rTensor M _ _ _

/--
theorem `lTensor_trans_congr` / 定理 `lTensor_trans_congr`

English:
theorem lTensor_trans_congr
  given: (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) (g' : S ≃ₗ[R] N)
  proof: toLinearMap_injective LinearMap.map_comp_lTensor M _ _ _

中文:
定理 lTensor_trans_congr
  条件: (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) (g' : S ≃ₗ[R] N)
  证明: toLinearMap_injective LinearMap.map_comp_lTensor M _ _ _
-/
@[simp] theorem lTensor_trans_congr (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) (g' : S ≃ₗ[R] N) :
    g'.lTensor _ ≪≫ₗ TensorProduct.congr f g = TensorProduct.congr f (g' ≪≫ₗ g) :=
toLinearMap_injective LinearMap.map_comp_lTensor M _ _ _

/--
theorem `congr_trans_rTensor` / 定理 `congr_trans_rTensor`

English:
theorem congr_trans_rTensor
  given: (f' : P ≃ₗ[R] S) (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q)
  proof: toLinearMap_injective LinearMap.rTensor_comp_map M _ _ _

中文:
定理 congr_trans_rTensor
  条件: (f' : P ≃ₗ[R] S) (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q)
  证明: toLinearMap_injective LinearMap.rTensor_comp_map M _ _ _
-/
@[simp] theorem congr_trans_rTensor (f' : P ≃ₗ[R] S) (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) :
    TensorProduct.congr f g ≪≫ₗ f'.rTensor _ = TensorProduct.congr (f ≪≫ₗ f') g :=
toLinearMap_injective LinearMap.rTensor_comp_map M _ _ _

/--
theorem `congr_trans_lTensor` / 定理 `congr_trans_lTensor`

English:
theorem congr_trans_lTensor
  given: (g' : Q ≃ₗ[R] S) (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q)
  proof: toLinearMap_injective LinearMap.lTensor_comp_map M _ _ _

中文:
定理 congr_trans_lTensor
  条件: (g' : Q ≃ₗ[R] S) (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q)
  证明: toLinearMap_injective LinearMap.lTensor_comp_map M _ _ _
-/
@[simp] theorem congr_trans_lTensor (g' : Q ≃ₗ[R] S) (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) :
    TensorProduct.congr f g ≪≫ₗ g'.lTensor _ = TensorProduct.congr f (g ≪≫ₗ g') :=
toLinearMap_injective LinearMap.lTensor_comp_map M _ _ _

variable {M}

/--
theorem `rTensor_pow` / 定理 `rTensor_pow`

English:
theorem rTensor_pow
  given: (f : M ≃ₗ[R] M) (n : Nat)
  statement: f.rTensor N ^ n = (f ^ n).rTensor N
  proof: by
  simpa only [one_pow] using! TensorProduct.congr_pow f (1 : N ≃ₗ[R] N) n

中文:
定理 rTensor_pow
  条件: (f : M ≃ₗ[R] M) (n : 自然数)
  结论: f.rTensor N ^ n = (f ^ n).rTensor N
  证明: by
  simpa only [one_pow] using! TensorProduct.congr_pow f (1 : N ≃ₗ[R] N) n
-/
@[simp] theorem rTensor_pow (f : M ≃ₗ[R] M) (n : Nat) : f.rTensor N ^ n = (f ^ n).rTensor N := by
  simpa only [one_pow] using! TensorProduct.congr_pow f (1 : N ≃ₗ[R] N) n

/--
theorem `rTensor_zpow` / 定理 `rTensor_zpow`

English:
theorem rTensor_zpow
  given: (f : M ≃ₗ[R] M) (n : Int)
  statement: f.rTensor N ^ n = (f ^ n).rTensor N
  proof: by
  simpa only [one_zpow] using! TensorProduct.congr_zpow f (1 : N ≃ₗ[R] N) n

中文:
定理 rTensor_zpow
  条件: (f : M ≃ₗ[R] M) (n : 整数)
  结论: f.rTensor N ^ n = (f ^ n).rTensor N
  证明: by
  simpa only [one_zpow] using! TensorProduct.congr_zpow f (1 : N ≃ₗ[R] N) n
-/
@[simp] theorem rTensor_zpow (f : M ≃ₗ[R] M) (n : Int) : f.rTensor N ^ n = (f ^ n).rTensor N := by
  simpa only [one_zpow] using! TensorProduct.congr_zpow f (1 : N ≃ₗ[R] N) n

/--
theorem `lTensor_pow` / 定理 `lTensor_pow`

English:
theorem lTensor_pow
  given: (f : N ≃ₗ[R] N) (n : Nat)
  statement: f.lTensor M ^ n = (f ^ n).lTensor M
  proof: by
  simpa only [one_pow] using! TensorProduct.congr_pow (1 : M ≃ₗ[R] M) f n

中文:
定理 lTensor_pow
  条件: (f : N ≃ₗ[R] N) (n : 自然数)
  结论: f.lTensor M ^ n = (f ^ n).lTensor M
  证明: by
  simpa only [one_pow] using! TensorProduct.congr_pow (1 : M ≃ₗ[R] M) f n
-/
@[simp] theorem lTensor_pow (f : N ≃ₗ[R] N) (n : Nat) : f.lTensor M ^ n = (f ^ n).lTensor M := by
  simpa only [one_pow] using! TensorProduct.congr_pow (1 : M ≃ₗ[R] M) f n

/--
theorem `lTensor_zpow` / 定理 `lTensor_zpow`

English:
theorem lTensor_zpow
  given: (f : N ≃ₗ[R] N) (n : Int)
  statement: f.lTensor M ^ n = (f ^ n).lTensor M
  proof: by
  simpa only [one_zpow] using! TensorProduct.congr_zpow (1 : M ≃ₗ[R] M) f n

中文:
定理 lTensor_zpow
  条件: (f : N ≃ₗ[R] N) (n : 整数)
  结论: f.lTensor M ^ n = (f ^ n).lTensor M
  证明: by
  simpa only [one_zpow] using! TensorProduct.congr_zpow (1 : M ≃ₗ[R] M) f n
-/
@[simp] theorem lTensor_zpow (f : N ≃ₗ[R] N) (n : Int) : f.lTensor M ^ n = (f ^ n).lTensor M := by
  simpa only [one_zpow] using! TensorProduct.congr_zpow (1 : M ≃ₗ[R] M) f n

end LinearEquiv

end Semiring

section Ring

variable {R : Type*} [CommSemiring R]
variable {M : Type*} {N : Type*} {P : Type*} {Q : Type*} {S : Type*}
variable [AddCommGroup M] [AddCommMonoid N] [AddCommGroup P] [AddCommMonoid Q]
variable [Module R M] [Module R N] [Module R P] [Module R Q]

namespace LinearMap

@[simp]
/--
theorem `lTensor_sub` / 定理 `lTensor_sub`

English:
theorem lTensor_sub
  given: (f g : N ->ₗ[R] P)
  statement: (f - g).lTensor M = f.lTensor M - g.lTensor M
  proof: by
  simp_rw [← coe_lTensorHom]
  exact (lTensorHom (R := R) (N := N) (P := P) M).map_sub f g

@[simp]

中文:
定理 lTensor_sub
  条件: (f g : N ->ₗ[R] P)
  结论: (f - g).lTensor M = f.lTensor M - g.lTensor M
  证明: by
  simp_rw [← coe_lTensorHom]
  exact (lTensorHom (R := R) (N := N) (P := P) M).map_sub f g

@[simp]

Depends on / 依赖: coe_lTensorHom, lTensorHom, map_sub, simp_rw
-/
theorem lTensor_sub (f g : N ->ₗ[R] P) : (f - g).lTensor M = f.lTensor M - g.lTensor M := by
  simp_rw [← coe_lTensorHom]
  exact (lTensorHom (R := R) (N := N) (P := P) M).map_sub f g

@[simp]
/--
theorem `rTensor_sub` / 定理 `rTensor_sub`

English:
theorem rTensor_sub
  given: (f g : N ->ₗ[R] P)
  statement: (f - g).rTensor Q = f.rTensor Q - g.rTensor Q
  proof: by
  simp only [← coe_rTensorHom]
  exact (rTensorHom (R := R) (N := N) (P := P) Q).map_sub f g

@[simp]

中文:
定理 rTensor_sub
  条件: (f g : N ->ₗ[R] P)
  结论: (f - g).rTensor Q = f.rTensor Q - g.rTensor Q
  证明: by
  simp only [← coe_rTensorHom]
  exact (rTensorHom (R := R) (N := N) (P := P) Q).map_sub f g

@[simp]

Depends on / 依赖: coe_rTensorHom, map_sub, rTensorHom
-/
theorem rTensor_sub (f g : N ->ₗ[R] P) : (f - g).rTensor Q = f.rTensor Q - g.rTensor Q := by
  simp only [← coe_rTensorHom]
  exact (rTensorHom (R := R) (N := N) (P := P) Q).map_sub f g

@[simp]
/--
theorem `lTensor_neg` / 定理 `lTensor_neg`

English:
theorem lTensor_neg
  given: (f : N ->ₗ[R] P)
  statement: (-f).lTensor M = -f.lTensor M
  proof: by
  simp only [← coe_lTensorHom]
  exact (lTensorHom (R := R) (N := N) (P := P) M).map_neg f

@[simp]

中文:
定理 lTensor_neg
  条件: (f : N ->ₗ[R] P)
  结论: (-f).lTensor M = -f.lTensor M
  证明: by
  simp only [← coe_lTensorHom]
  exact (lTensorHom (R := R) (N := N) (P := P) M).map_neg f

@[simp]

Depends on / 依赖: coe_lTensorHom, lTensorHom, map_neg
-/
theorem lTensor_neg (f : N ->ₗ[R] P) : (-f).lTensor M = -f.lTensor M := by
  simp only [← coe_lTensorHom]
  exact (lTensorHom (R := R) (N := N) (P := P) M).map_neg f

@[simp]
/--
theorem `rTensor_neg` / 定理 `rTensor_neg`

English:
theorem rTensor_neg
  given: (f : N ->ₗ[R] P)
  statement: (-f).rTensor Q = -f.rTensor Q
  proof: by
  simp only [← coe_rTensorHom]
  exact (rTensorHom (R := R) (N := N) (P := P) Q).map_neg f

中文:
定理 rTensor_neg
  条件: (f : N ->ₗ[R] P)
  结论: (-f).rTensor Q = -f.rTensor Q
  证明: by
  simp only [← coe_rTensorHom]
  exact (rTensorHom (R := R) (N := N) (P := P) Q).map_neg f

Depends on / 依赖: coe_rTensorHom, map_neg, rTensorHom
-/
theorem rTensor_neg (f : N ->ₗ[R] P) : (-f).rTensor Q = -f.rTensor Q := by
  simp only [← coe_rTensorHom]
  exact (rTensorHom (R := R) (N := N) (P := P) Q).map_neg f

end LinearMap

end Ring

namespace Equiv
variable {R A A' B B' : Type*} [CommSemiring R]
  [AddCommMonoid A'] [AddCommMonoid B'] [Module R A'] [Module R B']

variable (R) in
open TensorProduct in
/--
lemma `tensorProductComm_def` / 引理 `tensorProductComm_def`

English:
lemma tensorProductComm_def
  given: (eA : A ≃ A') (eB : B ≃ B')
  proof: eA.addCommMonoid
    letI := eB.addCommMonoid
    letI := eA.module R
    letI := eB.module R
    TensorProduct.comm R A B = .trans
      (congr (eA.linearEquiv R) (eB.linearEquiv R)) (.trans
(TensorProduct.comm R A' B') congr (eB.linearEquiv R).symm (eA.linearEquiv R).symm) := by
  ext x; induction

中文:
引理 tensorProductComm_def
  条件: (eA : A ≃ A') (eB : B ≃ B')
  证明: eA.addCommMonoid
    letI := eB.addCommMonoid
    letI := eA.module R
    letI := eB.module R
    TensorProduct.comm R A B = .trans
      (congr (eA.linearEquiv R) (eB.linearEquiv R)) (.trans
(TensorProduct.comm R A' B') congr (eB.linearEquiv R).symm (eA.linearEquiv R).symm) := by
  ext x; induction

Depends on / 依赖: addCommMonoid, eA.addCommMonoid
-/
lemma tensorProductComm_def (eA : A ≃ A') (eB : B ≃ B') :
    letI := eA.addCommMonoid
    letI := eB.addCommMonoid
    letI := eA.module R
    letI := eB.module R
    TensorProduct.comm R A B = .trans
      (congr (eA.linearEquiv R) (eB.linearEquiv R)) (.trans
(TensorProduct.comm R A' B') congr (eB.linearEquiv R).symm (eA.linearEquiv R).symm) := by
  ext x; induction x <;> simp [*]

end Equiv
