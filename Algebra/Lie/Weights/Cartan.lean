/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Lie.CartanSubalgebra
public import Mathlib.Algebra.Lie.Weights.Basic

/-!
# Weights and roots of Lie modules and Lie algebras with respect to Cartan subalgebras

Given a Lie algebra `L` which is not necessarily nilpotent, it may be useful to study its
representations by restricting them to a nilpotent subalgebra (e.g., a Cartan subalgebra). In the
particular case when we view `L` as a module over itself via the adjoint action, the weight spaces
of `L` restricted to a nilpotent subalgebra are known as root spaces.

Basic definitions and properties of the above ideas are provided in this file.

## Main definitions

  * `LieAlgebra.rootSpace`
  * `LieAlgebra.corootSpace`
  * `LieAlgebra.rootSpaceWeightSpaceProduct`
  * `LieAlgebra.rootSpaceProduct`
  * `LieAlgebra.zeroRootSubalgebra_eq_iff_is_cartan`

-/

@[expose] public section

open Set

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (H : LieSubalgebra R L) [LieRing.IsNilpotent H]
  {M : Type*} [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

namespace LieAlgebra

open scoped TensorProduct
open TensorProduct.LieModule LieModule

/--
Definition of `rootSpace` / `rootSpace` 的定义

English:
abbreviation rootSpace
  signature: (χ : H -> R)
  body: genWeightSpace L χ

中文:
缩写 rootSpace
  签名: (χ : H -> R)
  定义体: genWeightSpace L χ

Depends on / 依赖: genWeightSpace
-/
abbrev rootSpace (χ : H -> R) : LieSubmodule R H L :=
  genWeightSpace L χ

/--
theorem `zero_rootSpace_eq_top_of_nilpotent` / 定理 `zero_rootSpace_eq_top_of_nilpotent`

English:
theorem zero_rootSpace_eq_top_of_nilpotent
  given: [LieRing.IsNilpotent L]
  proof: zero_genWeightSpace_eq_top_of_nilpotent L

@[simp]

中文:
定理 zero_rootSpace_eq_top_of_nilpotent
  条件: [LieRing.IsNilpotent L]
  证明: zero_genWeightSpace_eq_top_of_nilpotent L

@[simp]

Depends on / 依赖: zero_genWeightSpace_eq_top_of_nilpotent
-/
theorem zero_rootSpace_eq_top_of_nilpotent [LieRing.IsNilpotent L] :
    rootSpace (⊤ : LieSubalgebra R L) 0 = ⊤ :=
  zero_genWeightSpace_eq_top_of_nilpotent L

@[simp]
/--
theorem `rootSpace_comap_eq_genWeightSpace` / 定理 `rootSpace_comap_eq_genWeightSpace`

English:
theorem rootSpace_comap_eq_genWeightSpace
  given: (χ : H -> R)
  proof: comap_genWeightSpace_eq_of_injective Subtype.coe_injective

中文:
定理 rootSpace_comap_eq_genWeightSpace
  条件: (χ : H -> R)
  证明: comap_genWeightSpace_eq_of_injective Subtype.coe_injective

Depends on / 依赖: Subtype, Subtype.coe_injective, coe_injective, comap_genWeightSpace_eq_of_injective
-/
theorem rootSpace_comap_eq_genWeightSpace (χ : H -> R) :
    (rootSpace H χ).comap H.incl' = genWeightSpace H χ :=
  comap_genWeightSpace_eq_of_injective Subtype.coe_injective

variable {H}

/--
theorem `lie_mem_genWeightSpace_of_mem_genWeightSpace` / 定理 `lie_mem_genWeightSpace_of_mem_genWeightSpace`

English:
theorem lie_mem_genWeightSpace_of_mem_genWeightSpace
  statement: {χ₁ χ₂ : H -> R} {x : L} {m : M}
  proof: by
  rw [genWeightSpace]; rw [LieSubmodule.mem_iInf]
  intro y
  replace hx : x in genWeightSpaceOf L (χ₁ y) y := by
    rw [rootSpace]; rw [genWeightSpace]; rw [LieSubmodule.mem_iInf] at hx; exact hx y
  replace hm : m in genWeightSpaceOf M (χ₂ y) y := by
    rw [genWeightSpace]; rw [LieSubmodule.m

中文:
定理 lie_mem_genWeightSpace_of_mem_genWeightSpace
  结论: {χ₁ χ₂ : H -> R} {x : L} {m : M}
  证明: by
  rw [genWeightSpace]; rw [LieSubmodule.mem_iInf]
  intro y
  replace hx : x in genWeightSpaceOf L (χ₁ y) y := by
    rw [rootSpace]; rw [genWeightSpace]; rw [LieSubmodule.mem_iInf] at hx; exact hx y
  replace hm : m in genWeightSpaceOf M (χ₂ y) y := by
    rw [genWeightSpace]; rw [LieSubmodule.m

Depends on / 依赖: LieSubmodule, LieSubmodule.mem_iInf, genWeightSpace, genWeightSpaceOf, lie_mem_maxGenEigenspace_toEnd, mem_iInf, replace, rootSpace
-/
theorem lie_mem_genWeightSpace_of_mem_genWeightSpace {χ₁ χ₂ : H -> R} {x : L} {m : M}
    (hx : x in rootSpace H χ₁) (hm : m in genWeightSpace M χ₂) :
    ⁅x, m⁆ in genWeightSpace M (χ₁ + χ₂) := by
  rw [genWeightSpace]; rw [LieSubmodule.mem_iInf]
  intro y
  replace hx : x in genWeightSpaceOf L (χ₁ y) y := by
    rw [rootSpace]; rw [genWeightSpace]; rw [LieSubmodule.mem_iInf] at hx; exact hx y
  replace hm : m in genWeightSpaceOf M (χ₂ y) y := by
    rw [genWeightSpace]; rw [LieSubmodule.mem_iInf] at hm; exact hm y
  exact lie_mem_maxGenEigenspace_toEnd hx hm

/--
lemma `toEnd_pow_apply_mem` / 引理 `toEnd_pow_apply_mem`

English:
lemma toEnd_pow_apply_mem
  statement: {χ₁ χ₂ : H -> R} {x : L} {m : M}
  proof: by
  induction n with
  | zero => simpa using hm
  | succ n IH =>
    simp only [pow_succ', Module.End.mul_apply, toEnd_apply_apply]
    convert! lie_mem_genWeightSpace_of_mem_genWeightSpace hx IH using 2
    rw [succ_nsmul]; rw [← add_assoc]; rw [add_comm (n • _)]

中文:
引理 toEnd_pow_apply_mem
  结论: {χ₁ χ₂ : H -> R} {x : L} {m : M}
  证明: by
  induction n with
  | zero => simpa using hm
  | succ n IH =>
    simp only [pow_succ', Module.End.mul_apply, toEnd_apply_apply]
    convert! lie_mem_genWeightSpace_of_mem_genWeightSpace hx IH using 2
    rw [succ_nsmul]; rw [← add_assoc]; rw [add_comm (n • _)]

Depends on / 依赖: Module, Module.End.mul_apply, add_assoc, add_comm, convert, lie_mem_genWeightSpace_of_mem_genWeightSpace, mul_apply, pow_succ, succ_nsmul, toEnd_apply_apply
-/
lemma toEnd_pow_apply_mem {χ₁ χ₂ : H -> R} {x : L} {m : M}
    (hx : x in rootSpace H χ₁) (hm : m in genWeightSpace M χ₂) (n) :
    (toEnd R L M x ^ n : Module.End R M) m in genWeightSpace M (n • χ₁ + χ₂) := by
  induction n with
  | zero => simpa using hm
  | succ n IH =>
    simp only [pow_succ', Module.End.mul_apply, toEnd_apply_apply]
    convert! lie_mem_genWeightSpace_of_mem_genWeightSpace hx IH using 2
    rw [succ_nsmul]; rw [← add_assoc]; rw [add_comm (n • _)]

/--
lemma `mem_biSup_genWeightSpace_of` / 引理 `mem_biSup_genWeightSpace_of`

English:
lemma mem_biSup_genWeightSpace_of
  statement: {s : Set (H -> R)} (hs : forallᵉ (χ₁ in s) (χ₂ in s), χ₁ + χ₂ in s)
  proof: by
  induction hx using LieSubmodule.iSup_induction' with
  | zero => simp
  | add _ _ _ _ hu hv => rw [add_lie]; exact add_mem hu hv
  | mem χ₁ u hu =>
    by_cases hχ₁ : χ₁ in s; swap
    · simp_all
    replace hu : u in rootSpace H χ₁ := by simpa [hχ₁] using hu
    induction hm using LieSubmodule

中文:
引理 mem_biSup_genWeightSpace_of
  结论: {s : Set (H -> R)} (hs : 对任意ᵉ (χ₁ in s) (χ₂ in s), χ₁ + χ₂ in s)
  证明: by
  induction hx using LieSubmodule.iSup_induction' with
  | zero => simp
  | add _ _ _ _ hu hv => rw [add_lie]; exact add_mem hu hv
  | mem χ₁ u hu =>
    by_cases hχ₁ : χ₁ in s; swap
    · simp_all
    replace hu : u in rootSpace H χ₁ := by simpa [hχ₁] using hu
    induction hm using LieSubmodule

Depends on / 依赖: LieSubmodule, LieSubmodule.iSup_induction, LieSubmodule.mem_iSup_of_mem, add_lie, add_mem, iSup_induction, lie_add, lie_mem_genWeightS, mem_iSup_of_mem, replace, rootSpace
-/
lemma mem_biSup_genWeightSpace_of {s : Set (H -> R)} (hs : forallᵉ (χ₁ in s) (χ₂ in s), χ₁ + χ₂ in s)
    {x : L} {m : M} (hx : x in ⨆ χ, ⨆ (_ : χ in s), rootSpace H χ)
    (hm : m in ⨆ χ, ⨆ (_ : χ in s), genWeightSpace M χ) :
    ⁅x, m⁆ in ⨆ χ, ⨆ (_ : χ in s), genWeightSpace M χ := by
  induction hx using LieSubmodule.iSup_induction' with
  | zero => simp
  | add _ _ _ _ hu hv => rw [add_lie]; exact add_mem hu hv
  | mem χ₁ u hu =>
    by_cases hχ₁ : χ₁ in s; swap
    · simp_all
    replace hu : u in rootSpace H χ₁ := by simpa [hχ₁] using hu
    induction hm using LieSubmodule.iSup_induction' with
    | zero => simp
    | add _ _ _ _ hv hw => rw [lie_add]; exact add_mem hv hw
    | mem χ₂ v hv =>
      by_cases hχ₂ : χ₂ in s; swap
      · simp_all
      apply LieSubmodule.mem_iSup_of_mem (χ₁ + χ₂)
      simp_all [lie_mem_genWeightSpace_of_mem_genWeightSpace]

variable (R L H M)

/--
Definition of `rootSpaceWeightSpaceProductAux` / `rootSpaceWeightSpaceProductAux` 的定义

English:
definition rootSpaceWeightSpaceProductAux
  signature: {χ₁ χ₂ χ₃ : H -> R} (hχ : χ₁ + χ₂ = χ₃)
  body: { toFun := fun m =>
        ⟨⁅(x : L), (m : M)⁆,
          hχ ▸ lie_mem_genWeightSpace_of_mem_genWeightSpace x.property m.property⟩
      map_add' := fun m n => by simp only [LieSubmodule.coe_add, lie_add, AddMemClass.mk_add_mk]
      map_smul' := fun t m => by simp }
  map_add' x y := by
    ext m


中文:
定义 rootSpaceWeightSpaceProductAux
  签名: {χ₁ χ₂ χ₃ : H -> R} (hχ : χ₁ + χ₂ = χ₃)
  定义体: { toFun := fun m =>
        ⟨⁅(x : L), (m : M)⁆,
          hχ ▸ lie_mem_genWeightSpace_of_mem_genWeightSpace x.property m.property⟩
      map_add' := fun m n => by simp only [LieSubmodule.coe_add, lie_add, AddMemClass.mk_add_mk]
      map_smul' := fun t m => by simp }
  map_add' x y := by
    ext m


Depends on / 依赖: AddHom, AddHom.coe_mk, AddMemClass, AddMemClass.mk_add_mk, LieSubmodule, LieSubmodule.coe_add, LinearMap, LinearMap.add_apply, LinearMap.coe_mk, RingHom, RingHom.id_apply, SetLike, SetLike.val_smul, add_apply, add_lie, coe_add, coe_mk, id_apply, lie_add, lie_mem_genWeightSpace_of_mem_genWeightSpace
-/
def rootSpaceWeightSpaceProductAux {χ₁ χ₂ χ₃ : H -> R} (hχ : χ₁ + χ₂ = χ₃) :
    rootSpace H χ₁ ->ₗ[R] genWeightSpace M χ₂ ->ₗ[R] genWeightSpace M χ₃ where
  toFun x :=
    { toFun := fun m =>
        ⟨⁅(x : L), (m : M)⁆,
          hχ ▸ lie_mem_genWeightSpace_of_mem_genWeightSpace x.property m.property⟩
      map_add' := fun m n => by simp only [LieSubmodule.coe_add, lie_add, AddMemClass.mk_add_mk]
      map_smul' := fun t m => by simp }
  map_add' x y := by
    ext m
    simp only [LieSubmodule.coe_add, add_lie, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply,
      AddMemClass.mk_add_mk]
  map_smul' t x := by
    simp only [RingHom.id_apply]
    ext m
    simp only [SetLike.val_smul, smul_lie, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply,
      SetLike.mk_smul_mk]

/--
Definition of `rootSpaceWeightSpaceProduct` / `rootSpaceWeightSpaceProduct` 的定义

English:
definition rootSpaceWeightSpaceProduct
  signature: (χ₁ χ₂ χ₃ : H -> R) (hχ : χ₁ + χ₂ = χ₃)
  body: liftLie R H (rootSpace H χ₁) (genWeightSpace M χ₂) (genWeightSpace M χ₃)
    { toLinearMap := rootSpaceWeightSpaceProductAux R L H M hχ
      map_lie' := fun {x y} => by
        ext m
        simp only [rootSpaceWeightSpaceProductAux]
        dsimp
        simp only [lie_lie] }

@[simp]

中文:
定义 rootSpaceWeightSpaceProduct
  签名: (χ₁ χ₂ χ₃ : H -> R) (hχ : χ₁ + χ₂ = χ₃)
  定义体: liftLie R H (rootSpace H χ₁) (genWeightSpace M χ₂) (genWeightSpace M χ₃)
    { toLinearMap := rootSpaceWeightSpaceProductAux R L H M hχ
      map_lie' := fun {x y} => by
        ext m
        simp only [rootSpaceWeightSpaceProductAux]
        dsimp
        simp only [lie_lie] }

@[simp]

Depends on / 依赖: genWeightSpace, lie_lie, liftLie, map_lie, rootSpace, rootSpaceWeightSpaceProductAux, toLinearMap
-/
def rootSpaceWeightSpaceProduct (χ₁ χ₂ χ₃ : H -> R) (hχ : χ₁ + χ₂ = χ₃) :
    rootSpace H χ₁ otimes[R] genWeightSpace M χ₂ ->ₗ⁅R,H⁆ genWeightSpace M χ₃ :=
  liftLie R H (rootSpace H χ₁) (genWeightSpace M χ₂) (genWeightSpace M χ₃)
    { toLinearMap := rootSpaceWeightSpaceProductAux R L H M hχ
      map_lie' := fun {x y} => by
        ext m
        simp only [rootSpaceWeightSpaceProductAux]
        dsimp
        simp only [lie_lie] }

@[simp]
/--
theorem `coe_rootSpaceWeightSpaceProduct_tmul` / 定理 `coe_rootSpaceWeightSpaceProduct_tmul`

English:
theorem coe_rootSpaceWeightSpaceProduct_tmul
  statement: (χ₁ χ₂ χ₃ : H -> R) (hχ : χ₁ + χ₂ = χ₃)
  proof: by
  simp only [rootSpaceWeightSpaceProduct, rootSpaceWeightSpaceProductAux, coe_liftLie_eq_lift_coe,
    lift_apply, LinearMap.coe_mk, AddHom.coe_mk]

中文:
定理 coe_rootSpaceWeightSpaceProduct_tmul
  结论: (χ₁ χ₂ χ₃ : H -> R) (hχ : χ₁ + χ₂ = χ₃)
  证明: by
  simp only [rootSpaceWeightSpaceProduct, rootSpaceWeightSpaceProductAux, coe_liftLie_eq_lift_coe,
    lift_apply, LinearMap.coe_mk, AddHom.coe_mk]

Depends on / 依赖: AddHom, AddHom.coe_mk, LinearMap, LinearMap.coe_mk, coe_liftLie_eq_lift_coe, coe_mk, lift_apply, rootSpaceWeightSpaceProduct, rootSpaceWeightSpaceProductAux
-/
theorem coe_rootSpaceWeightSpaceProduct_tmul (χ₁ χ₂ χ₃ : H -> R) (hχ : χ₁ + χ₂ = χ₃)
    (x : rootSpace H χ₁) (m : genWeightSpace M χ₂) :
    (rootSpaceWeightSpaceProduct R L H M χ₁ χ₂ χ₃ hχ (x otimesₜ m) : M) = ⁅(x : L), (m : M)⁆ := by
  simp only [rootSpaceWeightSpaceProduct, rootSpaceWeightSpaceProductAux, coe_liftLie_eq_lift_coe,
    lift_apply, LinearMap.coe_mk, AddHom.coe_mk]

/--
theorem `mapsTo_toEnd_genWeightSpace_add_of_mem_rootSpace` / 定理 `mapsTo_toEnd_genWeightSpace_add_of_mem_rootSpace`

English:
theorem mapsTo_toEnd_genWeightSpace_add_of_mem_rootSpace
  statement: (α χ : H -> R)
  proof: by
  intro m hm
  let x' : rootSpace H α := ⟨x, hx⟩
  let m' : genWeightSpace M χ := ⟨m, hm⟩
  exact (rootSpaceWeightSpaceProduct R L H M α χ (α + χ) rfl (x' otimesₜ m')).property

中文:
定理 mapsTo_toEnd_genWeightSpace_add_of_mem_rootSpace
  结论: (α χ : H -> R)
  证明: by
  intro m hm
  let x' : rootSpace H α := ⟨x, hx⟩
  let m' : genWeightSpace M χ := ⟨m, hm⟩
  exact (rootSpaceWeightSpaceProduct R L H M α χ (α + χ) rfl (x' otimesₜ m')).property

Depends on / 依赖: genWeightSpace, property, rootSpace, rootSpaceWeightSpaceProduct
-/
theorem mapsTo_toEnd_genWeightSpace_add_of_mem_rootSpace (α χ : H -> R)
    {x : L} (hx : x in rootSpace H α) :
    MapsTo (toEnd R L M x) (genWeightSpace M χ) (genWeightSpace M (α + χ)) := by
  intro m hm
  let x' : rootSpace H α := ⟨x, hx⟩
  let m' : genWeightSpace M χ := ⟨m, hm⟩
  exact (rootSpaceWeightSpaceProduct R L H M α χ (α + χ) rfl (x' otimesₜ m')).property

/--
Definition of `rootSpaceProduct` / `rootSpaceProduct` 的定义

English:
definition rootSpaceProduct
  signature: (χ₁ χ₂ χ₃ : H -> R) (hχ : χ₁ + χ₂ = χ₃)
  body: rootSpaceWeightSpaceProduct R L H L χ₁ χ₂ χ₃ hχ

@[simp]

中文:
定义 rootSpaceProduct
  签名: (χ₁ χ₂ χ₃ : H -> R) (hχ : χ₁ + χ₂ = χ₃)
  定义体: rootSpaceWeightSpaceProduct R L H L χ₁ χ₂ χ₃ hχ

@[simp]

Depends on / 依赖: rootSpaceWeightSpaceProduct
-/
def rootSpaceProduct (χ₁ χ₂ χ₃ : H -> R) (hχ : χ₁ + χ₂ = χ₃) :
    rootSpace H χ₁ otimes[R] rootSpace H χ₂ ->ₗ⁅R,H⁆ rootSpace H χ₃ :=
  rootSpaceWeightSpaceProduct R L H L χ₁ χ₂ χ₃ hχ

@[simp]
/--
theorem `rootSpaceProduct_def` / 定理 `rootSpaceProduct_def`

English:
theorem rootSpaceProduct_def
  statement: rootSpaceProduct R L H = rootSpaceWeightSpaceProduct R L H L
  proof: rfl

中文:
定理 rootSpaceProduct_def
  结论: rootSpaceProduct R L H = rootSpaceWeightSpaceProduct R L H L
  证明: rfl
-/
theorem rootSpaceProduct_def : rootSpaceProduct R L H = rootSpaceWeightSpaceProduct R L H L := rfl

/--
theorem `rootSpaceProduct_tmul` / 定理 `rootSpaceProduct_tmul`

English:
theorem rootSpaceProduct_tmul
  proof: by
  simp only [rootSpaceProduct_def, coe_rootSpaceWeightSpaceProduct_tmul]

中文:
定理 rootSpaceProduct_tmul
  证明: by
  simp only [rootSpaceProduct_def, coe_rootSpaceWeightSpaceProduct_tmul]

Depends on / 依赖: coe_rootSpaceWeightSpaceProduct_tmul, rootSpaceProduct_def
-/
theorem rootSpaceProduct_tmul
    (χ₁ χ₂ χ₃ : H -> R) (hχ : χ₁ + χ₂ = χ₃) (x : rootSpace H χ₁) (y : rootSpace H χ₂) :
    (rootSpaceProduct R L H χ₁ χ₂ χ₃ hχ (x otimesₜ y) : L) = ⁅(x : L), (y : L)⁆ := by
  simp only [rootSpaceProduct_def, coe_rootSpaceWeightSpaceProduct_tmul]

/--
Definition of `zeroRootSubalgebra` / `zeroRootSubalgebra` 的定义

English:
definition zeroRootSubalgebra
  signature: : LieSubalgebra R L
  body: { toSubmodule := (rootSpace H 0 : Submodule R L)
    lie_mem' := fun {x y hx hy} => by
      let xy : rootSpace H 0 otimes[R] rootSpace H 0 := ⟨x, hx⟩ otimesₜ ⟨y, hy⟩
      suffices (rootSpaceProduct R L H 0 0 0 (add_zero 0) xy : L) in rootSpace H 0 by
        rwa [rootSpaceProduct_tmul, Subtype.coe

中文:
定义 zeroRootSubalgebra
  签名: : LieSubalgebra R L
  定义体: { toSubmodule := (rootSpace H 0 : Submodule R L)
    lie_mem' := fun {x y hx hy} => by
      let xy : rootSpace H 0 otimes[R] rootSpace H 0 := ⟨x, hx⟩ otimesₜ ⟨y, hy⟩
      suffices (rootSpaceProduct R L H 0 0 0 (add_zero 0) xy : L) in rootSpace H 0 by
        rwa [rootSpaceProduct_tmul, Subtype.coe

Depends on / 依赖: Submodule, Subtype, Subtype.coe_mk, add_zero, coe_mk, lie_mem, otimes, property, rootSpace, rootSpaceProduct, rootSpaceProduct_tmul, toSubmodule
-/
def zeroRootSubalgebra : LieSubalgebra R L :=
  { toSubmodule := (rootSpace H 0 : Submodule R L)
    lie_mem' := fun {x y hx hy} => by
      let xy : rootSpace H 0 otimes[R] rootSpace H 0 := ⟨x, hx⟩ otimesₜ ⟨y, hy⟩
      suffices (rootSpaceProduct R L H 0 0 0 (add_zero 0) xy : L) in rootSpace H 0 by
        rwa [rootSpaceProduct_tmul, Subtype.coe_mk, Subtype.coe_mk] at this
      exact (rootSpaceProduct R L H 0 0 0 (add_zero 0) xy).property }

@[simp]
/--
theorem `coe_zeroRootSubalgebra` / 定理 `coe_zeroRootSubalgebra`

English:
theorem coe_zeroRootSubalgebra
  statement: (zeroRootSubalgebra R L H : Submodule R L) = rootSpace H 0
  proof: rfl

中文:
定理 coe_zeroRootSubalgebra
  结论: (zeroRootSubalgebra R L H : Submodule R L) = rootSpace H 0
  证明: rfl
-/
theorem coe_zeroRootSubalgebra : (zeroRootSubalgebra R L H : Submodule R L) = rootSpace H 0 := rfl

/--
theorem `mem_zeroRootSubalgebra` / 定理 `mem_zeroRootSubalgebra`

English:
theorem mem_zeroRootSubalgebra
  given: (x : L)
  proof: by
  change x in rootSpace H 0 ↔ _
  simp only [mem_genWeightSpace, Pi.zero_apply, zero_smul, sub_zero]

中文:
定理 mem_zeroRootSubalgebra
  条件: (x : L)
  证明: by
  change x in rootSpace H 0 ↔ _
  simp only [mem_genWeightSpace, Pi.zero_apply, zero_smul, sub_zero]

Depends on / 依赖: Pi.zero_apply, mem_genWeightSpace, rootSpace, sub_zero, zero_apply, zero_smul
-/
theorem mem_zeroRootSubalgebra (x : L) :
    x in zeroRootSubalgebra R L H ↔ forall y : H, exists k : Nat, (toEnd R H L y ^ k) x = 0 := by
  change x in rootSpace H 0 ↔ _
  simp only [mem_genWeightSpace, Pi.zero_apply, zero_smul, sub_zero]

/--
theorem `toLieSubmodule_le_rootSpace_zero` / 定理 `toLieSubmodule_le_rootSpace_zero`

English:
theorem toLieSubmodule_le_rootSpace_zero
  statement: H.toLieSubmodule <= rootSpace H 0
  proof: by
  intro x hx
  simp only [LieSubalgebra.mem_toLieSubmodule] at hx
  simp only [mem_genWeightSpace, Pi.zero_apply, sub_zero, zero_smul]
  intro y
  obtain ⟨k, hk⟩ := IsNilpotent.nilpotent R H H
  use k
  let f : Module.End R H := toEnd R H H y
  let g : Module.End R L := toEnd R H L y
  have hfg :

中文:
定理 toLieSubmodule_le_rootSpace_zero
  结论: H.toLieSubmodule <= rootSpace H 0
  证明: by
  intro x hx
  simp only [LieSubalgebra.mem_toLieSubmodule] at hx
  simp only [mem_genWeightSpace, Pi.zero_apply, sub_zero, zero_smul]
  intro y
  obtain ⟨k, hk⟩ := IsNilpotent.nilpotent R H H
  use k
  let f : Module.End R H := toEnd R H H y
  let g : Module.End R L := toEnd R H L y
  have hfg :

Depends on / 依赖: IsNilpotent, IsNilpotent.nilpotent, LieSubalgebra, LieSubalgebra.mem_toLieSubmodule, Module, Module.End, Module.End.commute_pow_left_of_commute, Pi.zero_apply, Submodule, commute_pow_left_of_commute, g.comp, iterate_toEnd_mem_, mem_genWeightSpace, mem_toLieSubmodule, nilpotent, sub_zero, subtype, subtype.comp, zero_apply, zero_smul
-/
theorem toLieSubmodule_le_rootSpace_zero : H.toLieSubmodule <= rootSpace H 0 := by
  intro x hx
  simp only [LieSubalgebra.mem_toLieSubmodule] at hx
  simp only [mem_genWeightSpace, Pi.zero_apply, sub_zero, zero_smul]
  intro y
  obtain ⟨k, hk⟩ := IsNilpotent.nilpotent R H H
  use k
  let f : Module.End R H := toEnd R H H y
  let g : Module.End R L := toEnd R H L y
  have hfg : g.comp (H : Submodule R L).subtype = (H : Submodule R L).subtype.comp f := rfl
  change (g ^ k).comp (H : Submodule R L).subtype ⟨x, hx⟩ = 0
  rw [Module.End.commute_pow_left_of_commute hfg k]
  have h := iterate_toEnd_mem_lowerCentralSeries R H H y ⟨x, hx⟩ k
  rw [hk]; rw [LieSubmodule.mem_bot] at h
  simp only [Submodule.subtype_apply, Function.comp_apply, Module.End.pow_apply, LinearMap.coe_comp,
    Submodule.coe_eq_zero]
  exact h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nontrivial
  signature: H] : Nontrivial (genWeightSpace L (0 : H -> R))
  body: by
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, e⟩ := exists_pair_ne H
  exact ⟨⟨x, toLieSubmodule_le_rootSpace_zero R L H hx⟩,
    ⟨y, toLieSubmodule_le_rootSpace_zero R L H hy⟩, by simpa using e⟩

中文:
实例 [Nontrivial
  签名: H] : Nontrivial (genWeightSpace L (0 : H -> R))
  定义体: by
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, e⟩ := exists_pair_ne H
  exact ⟨⟨x, toLieSubmodule_le_rootSpace_zero R L H hx⟩,
    ⟨y, toLieSubmodule_le_rootSpace_zero R L H hy⟩, by simpa using e⟩

Depends on / 依赖: exists_pair_ne, toLieSubmodule_le_rootSpace_zero
-/
instance [Nontrivial H] : Nontrivial (genWeightSpace L (0 : H -> R)) := by
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, e⟩ := exists_pair_ne H
  exact ⟨⟨x, toLieSubmodule_le_rootSpace_zero R L H hx⟩,
    ⟨y, toLieSubmodule_le_rootSpace_zero R L H hy⟩, by simpa using e⟩

/--
theorem `le_zeroRootSubalgebra` / 定理 `le_zeroRootSubalgebra`

English:
theorem le_zeroRootSubalgebra
  statement: H <= zeroRootSubalgebra R L H
  proof: by
  rw [← LieSubalgebra.toSubmodule_le_toSubmodule]; rw [← H.coe_toLieSubmodule]; rw [coe_zeroRootSubalgebra]; rw [LieSubmodule.toSubmodule_le_toSubmodule]
  exact toLieSubmodule_le_rootSpace_zero R L H

@[simp]

中文:
定理 le_zeroRootSubalgebra
  结论: H <= zeroRootSubalgebra R L H
  证明: by
  rw [← LieSubalgebra.toSubmodule_le_toSubmodule]; rw [← H.coe_toLieSubmodule]; rw [coe_zeroRootSubalgebra]; rw [LieSubmodule.toSubmodule_le_toSubmodule]
  exact toLieSubmodule_le_rootSpace_zero R L H

@[simp]

Depends on / 依赖: H.coe_toLieSubmodule, LieSubalgebra, LieSubalgebra.toSubmodule_le_toSubmodule, LieSubmodule, LieSubmodule.toSubmodule_le_toSubmodule, coe_toLieSubmodule, coe_zeroRootSubalgebra, toLieSubmodule_le_rootSpace_zero, toSubmodule_le_toSubmodule
-/
theorem le_zeroRootSubalgebra : H <= zeroRootSubalgebra R L H := by
  rw [← LieSubalgebra.toSubmodule_le_toSubmodule]; rw [← H.coe_toLieSubmodule]; rw [coe_zeroRootSubalgebra]; rw [LieSubmodule.toSubmodule_le_toSubmodule]
  exact toLieSubmodule_le_rootSpace_zero R L H

@[simp]
/--
theorem `zeroRootSubalgebra_normalizer_eq_self` / 定理 `zeroRootSubalgebra_normalizer_eq_self`

English:
theorem zeroRootSubalgebra_normalizer_eq_self
  proof: by
  refine le_antisymm ?_ (LieSubalgebra.le_normalizer _)
  intro x hx
  rw [LieSubalgebra.mem_normalizer_iff] at hx
  rw [mem_zeroRootSubalgebra]
  rintro ⟨y, hy⟩
  specialize hx y (le_zeroRootSubalgebra R L H hy)
  rw [mem_zeroRootSubalgebra] at hx
  obtain ⟨k, hk⟩ := hx ⟨y, hy⟩
  rw [← lie_skew]

中文:
定理 zeroRootSubalgebra_normalizer_eq_self
  证明: by
  refine le_antisymm ?_ (LieSubalgebra.le_normalizer _)
  intro x hx
  rw [LieSubalgebra.mem_normalizer_iff] at hx
  rw [mem_zeroRootSubalgebra]
  rintro ⟨y, hy⟩
  specialize hx y (le_zeroRootSubalgebra R L H hy)
  rw [mem_zeroRootSubalgebra] at hx
  obtain ⟨k, hk⟩ := hx ⟨y, hy⟩
  rw [← lie_skew]

Depends on / 依赖: Function, Function.comp_apply, LieSubalgebra, LieSubalgebra.coe_bracket_of_module, LieSubalgebra.le_normalizer, LieSubalgebra.mem_normalizer_iff, LinearMap, LinearMap.coe_comp, Module, Module.End.iterate_succ, Submodule, Submodule.coe_mk, coe_bracket_of_module, coe_comp, coe_mk, comp_apply, iterate_succ, le_antisymm, le_normalizer, le_zeroRootSubalgebra
-/
theorem zeroRootSubalgebra_normalizer_eq_self :
    (zeroRootSubalgebra R L H).normalizer = zeroRootSubalgebra R L H := by
  refine le_antisymm ?_ (LieSubalgebra.le_normalizer _)
  intro x hx
  rw [LieSubalgebra.mem_normalizer_iff] at hx
  rw [mem_zeroRootSubalgebra]
  rintro ⟨y, hy⟩
  specialize hx y (le_zeroRootSubalgebra R L H hy)
  rw [mem_zeroRootSubalgebra] at hx
  obtain ⟨k, hk⟩ := hx ⟨y, hy⟩
  rw [← lie_skew]; rw [map_neg]; rw [neg_eq_zero] at hk
  use k + 1
  rw [Module.End.iterate_succ]; rw [LinearMap.coe_comp]; rw [Function.comp_apply]; rw [toEnd_apply_apply]; rw [LieSubalgebra.coe_bracket_of_module]; rw [Submodule.coe_mk]; rw [hk]

/--
theorem `is_cartan_of_zeroRootSubalgebra_eq` / 定理 `is_cartan_of_zeroRootSubalgebra_eq`

English:
theorem is_cartan_of_zeroRootSubalgebra_eq
  given: (h : zeroRootSubalgebra R L H = H)
  proof: { nilpotent := inferInstance
    self_normalizing := by rw [← h]; exact zeroRootSubalgebra_normalizer_eq_self R L H }

@[simp]

中文:
定理 is_cartan_of_zeroRootSubalgebra_eq
  条件: (h : zeroRootSubalgebra R L H = H)
  证明: { nilpotent := inferInstance
    self_normalizing := by rw [← h]; exact zeroRootSubalgebra_normalizer_eq_self R L H }

@[simp]

Depends on / 依赖: nilpotent, self_normalizing, zeroRootSubalgebra_normalizer_eq_self
-/
theorem is_cartan_of_zeroRootSubalgebra_eq (h : zeroRootSubalgebra R L H = H) :
    H.IsCartanSubalgebra :=
  { nilpotent := inferInstance
    self_normalizing := by rw [← h]; exact zeroRootSubalgebra_normalizer_eq_self R L H }

@[simp]
/--
theorem `zeroRootSubalgebra_eq_of_is_cartan` / 定理 `zeroRootSubalgebra_eq_of_is_cartan`

English:
theorem zeroRootSubalgebra_eq_of_is_cartan
  statement: (H : LieSubalgebra R L) [H.IsCartanSubalgebra]
  proof: by
  refine le_antisymm ?_ (le_zeroRootSubalgebra R L H)
  suffices rootSpace H 0 <= H.toLieSubmodule by exact fun x hx => this hx
  obtain ⟨k, hk⟩ := (rootSpace H 0).isNilpotent_iff_exists_self_le_ucs.mp (by infer_instance)
  exact hk.trans (LieSubmodule.ucs_le_of_normalizer_eq_self (by simp) k)

中文:
定理 zeroRootSubalgebra_eq_of_is_cartan
  结论: (H : LieSubalgebra R L) [H.IsCartanSubalgebra]
  证明: by
  refine le_antisymm ?_ (le_zeroRootSubalgebra R L H)
  suffices rootSpace H 0 <= H.toLieSubmodule by exact fun x hx => this hx
  obtain ⟨k, hk⟩ := (rootSpace H 0).isNilpotent_iff_exists_self_le_ucs.mp (by infer_instance)
  exact hk.trans (LieSubmodule.ucs_le_of_normalizer_eq_self (by simp) k)

Depends on / 依赖: H.toLieSubmodule, LieSubmodule, LieSubmodule.ucs_le_of_normalizer_eq_self, hk.trans, infer_instance, isNilpotent_iff_exists_self_le_ucs, isNilpotent_iff_exists_self_le_ucs.mp, le_antisymm, le_zeroRootSubalgebra, rootSpace, toLieSubmodule, ucs_le_of_normalizer_eq_self
-/
theorem zeroRootSubalgebra_eq_of_is_cartan (H : LieSubalgebra R L) [H.IsCartanSubalgebra]
    [IsNoetherian R L] : zeroRootSubalgebra R L H = H := by
  refine le_antisymm ?_ (le_zeroRootSubalgebra R L H)
  suffices rootSpace H 0 <= H.toLieSubmodule by exact fun x hx => this hx
  obtain ⟨k, hk⟩ := (rootSpace H 0).isNilpotent_iff_exists_self_le_ucs.mp (by infer_instance)
  exact hk.trans (LieSubmodule.ucs_le_of_normalizer_eq_self (by simp) k)

/--
theorem `zeroRootSubalgebra_eq_iff_is_cartan` / 定理 `zeroRootSubalgebra_eq_iff_is_cartan`

English:
theorem zeroRootSubalgebra_eq_iff_is_cartan
  given: [IsNoetherian R L]
  proof: ⟨is_cartan_of_zeroRootSubalgebra_eq R L H, by intros; simp⟩

中文:
定理 zeroRootSubalgebra_eq_iff_is_cartan
  条件: [IsNoetherian R L]
  证明: ⟨is_cartan_of_zeroRootSubalgebra_eq R L H, by intros; simp⟩

Depends on / 依赖: intros, is_cartan_of_zeroRootSubalgebra_eq
-/
theorem zeroRootSubalgebra_eq_iff_is_cartan [IsNoetherian R L] :
    zeroRootSubalgebra R L H = H ↔ H.IsCartanSubalgebra :=
  ⟨is_cartan_of_zeroRootSubalgebra_eq R L H, by intros; simp⟩

/--
theorem `eq_rootSpace_zero_iff_isCartan` / 定理 `eq_rootSpace_zero_iff_isCartan`

English:
theorem eq_rootSpace_zero_iff_isCartan
  given: [IsNoetherian R L]
  proof: by
  rw [← zeroRootSubalgebra_eq_iff_is_cartan]; rw [← LieSubalgebra.toSubmodule_inj]; rw [← LieSubmodule.toSubmodule_inj]
  aesop

@[simp]

中文:
定理 eq_rootSpace_zero_iff_isCartan
  条件: [IsNoetherian R L]
  证明: by
  rw [← zeroRootSubalgebra_eq_iff_is_cartan]; rw [← LieSubalgebra.toSubmodule_inj]; rw [← LieSubmodule.toSubmodule_inj]
  aesop

@[simp]

Depends on / 依赖: LieSubalgebra, LieSubalgebra.toSubmodule_inj, LieSubmodule, LieSubmodule.toSubmodule_inj, toSubmodule_inj, zeroRootSubalgebra_eq_iff_is_cartan
-/
theorem eq_rootSpace_zero_iff_isCartan [IsNoetherian R L] :
    H.toLieSubmodule = rootSpace H 0 ↔ H.IsCartanSubalgebra := by
  rw [← zeroRootSubalgebra_eq_iff_is_cartan]; rw [← LieSubalgebra.toSubmodule_inj]; rw [← LieSubmodule.toSubmodule_inj]
  aesop

@[simp]
/--
theorem `rootSpace_zero_eq` / 定理 `rootSpace_zero_eq`

English:
theorem rootSpace_zero_eq
  given: (H : LieSubalgebra R L) [H.IsCartanSubalgebra] [IsNoetherian R L]
  proof: by
  rw [← LieSubmodule.toSubmodule_inj]; rw [← coe_zeroRootSubalgebra]; rw [zeroRootSubalgebra_eq_of_is_cartan R L H]; rw [LieSubalgebra.coe_toLieSubmodule]

中文:
定理 rootSpace_zero_eq
  条件: (H : LieSubalgebra R L) [H.IsCartanSubalgebra] [IsNoetherian R L]
  证明: by
  rw [← LieSubmodule.toSubmodule_inj]; rw [← coe_zeroRootSubalgebra]; rw [zeroRootSubalgebra_eq_of_is_cartan R L H]; rw [LieSubalgebra.coe_toLieSubmodule]

Depends on / 依赖: LieSubalgebra, LieSubalgebra.coe_toLieSubmodule, LieSubmodule, LieSubmodule.toSubmodule_inj, coe_toLieSubmodule, coe_zeroRootSubalgebra, toSubmodule_inj, zeroRootSubalgebra_eq_of_is_cartan
-/
theorem rootSpace_zero_eq (H : LieSubalgebra R L) [H.IsCartanSubalgebra] [IsNoetherian R L] :
    rootSpace H 0 = H.toLieSubmodule := by
  rw [← LieSubmodule.toSubmodule_inj]; rw [← coe_zeroRootSubalgebra]; rw [zeroRootSubalgebra_eq_of_is_cartan R L H]; rw [LieSubalgebra.coe_toLieSubmodule]

variable {R L H}
variable [H.IsCartanSubalgebra] [IsNoetherian R L] (α : H -> R)

/--
Definition of `corootSpace` / `corootSpace` 的定义

English:
definition corootSpace
  signature: : LieIdeal R H
  body: LieModuleHom.range ((rootSpace H 0).incl.comp <|
    rootSpaceProduct R L H α (-α) 0 (add_neg_cancel α)).codRestrict H.toLieSubmodule (by
  rw [← rootSpace_zero_eq]
  exact fun p => (rootSpaceProduct R L H α (-α) 0 (add_neg_cancel α) p).property)

中文:
定义 corootSpace
  签名: : LieIdeal R H
  定义体: LieModuleHom.range ((rootSpace H 0).incl.comp <|
    rootSpaceProduct R L H α (-α) 0 (add_neg_cancel α)).codRestrict H.toLieSubmodule (by
  rw [← rootSpace_zero_eq]
  exact fun p => (rootSpaceProduct R L H α (-α) 0 (add_neg_cancel α) p).property)

Depends on / 依赖: H.toLieSubmodule, LieModuleHom, LieModuleHom.range, add_neg_cancel, codRestrict, incl.comp, property, rootSpace, rootSpaceProduct, rootSpace_zero_eq, toLieSubmodule
-/
def corootSpace : LieIdeal R H :=
LieModuleHom.range ((rootSpace H 0).incl.comp <|
    rootSpaceProduct R L H α (-α) 0 (add_neg_cancel α)).codRestrict H.toLieSubmodule (by
  rw [← rootSpace_zero_eq]
  exact fun p => (rootSpaceProduct R L H α (-α) 0 (add_neg_cancel α) p).property)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `mem_corootSpace` / 引理 `mem_corootSpace`

English:
lemma mem_corootSpace
  given: {x : H}
  proof: by
  have : x in corootSpace α ↔
      (x : L) in LieSubmodule.map H.toLieSubmodule.incl (corootSpace α) := by
    rw [corootSpace]
    simp only [rootSpaceProduct_def, LieModuleHom.mem_range, LieSubmodule.mem_map,
      LieSubmodule.incl_apply, SetLike.coe_eq_coe, exists_eq_right]
    rfl
  simp_rw

中文:
引理 mem_corootSpace
  条件: {x : H}
  证明: by
  have : x in corootSpace α ↔
      (x : L) in LieSubmodule.map H.toLieSubmodule.incl (corootSpace α) := by
    rw [corootSpace]
    simp only [rootSpaceProduct_def, LieModuleHom.mem_range, LieSubmodule.mem_map,
      LieSubmodule.incl_apply, SetLike.coe_eq_coe, exists_eq_right]
    rfl
  simp_rw

Depends on / 依赖: H.toLieSubmodule.incl, LieModuleHom, LieModuleHom.map_top, LieModuleHom.mem_range, LieSubmodule, LieSubmodule.incl_apply, LieSubmodule.map, LieSubmodule.mem_map, LieSubmodule.mem_toSubmodule, LieSubmodule.toSubmodule_map, LieSubmodule.top_toSubmodule, LinearMap, LinearMap.map_span, Set.image, Set.mem_ofPred_eq, SetLike, SetLike.coe_eq_coe, TensorProduct, TensorProduct.span_tmul_eq_top, coe_eq_coe
-/
lemma mem_corootSpace {x : H} :
    x in corootSpace α ↔
    (x : L) in Submodule.span R {⁅y, z⁆ | (y in rootSpace H α) (z in rootSpace H (-α))} := by
  have : x in corootSpace α ↔
      (x : L) in LieSubmodule.map H.toLieSubmodule.incl (corootSpace α) := by
    rw [corootSpace]
    simp only [rootSpaceProduct_def, LieModuleHom.mem_range, LieSubmodule.mem_map,
      LieSubmodule.incl_apply, SetLike.coe_eq_coe, exists_eq_right]
    rfl
  simp_rw [this, corootSpace, ← LieModuleHom.map_top, ← LieSubmodule.mem_toSubmodule,
    LieSubmodule.toSubmodule_map, LieSubmodule.top_toSubmodule, ← TensorProduct.span_tmul_eq_top,
    LinearMap.map_span, Set.image, Set.mem_ofPred_eq, exists_exists_exists_and_eq]
  change (x : L) in Submodule.span R
    {x | exists (a : rootSpace H α) (b : rootSpace H (-α)), ⁅(a : L), (b : L)⁆ = x} ↔ _
  simp

/--
lemma `mem_corootSpace'` / 引理 `mem_corootSpace'`

English:
lemma mem_corootSpace'
  given: {x : H}
  proof: by
  set s : Set H := ({⁅y, z⁆ | (y in rootSpace H α) (z in rootSpace H (-α))} : Set H)
  suffices H.subtype '' s = {⁅y, z⁆ | (y in rootSpace H α) (z in rootSpace H (-α))} by
    erw [← (H : Submodule R L).injective_subtype.mem_set_image (s := Submodule.span R s)]
    rw [mem_image]
    simp_rw [Set

中文:
引理 mem_corootSpace'
  条件: {x : H}
  证明: by
  set s : Set H := ({⁅y, z⁆ | (y in rootSpace H α) (z in rootSpace H (-α))} : Set H)
  suffices H.subtype '' s = {⁅y, z⁆ | (y in rootSpace H α) (z in rootSpace H (-α))} by
    erw [← (H : Submodule R L).injective_subtype.mem_set_image (s := Submodule.span R s)]
    rw [mem_image]
    simp_rw [Set

Depends on / 依赖: H.subtype, LieSubalgebra, LieSubalgebra.mem_toSu, SetLike, SetLike.mem_coe, Submodule, Submodule.coe_subtype, Submodule.map_span, Submodule.mem_map, Submodule.span, Subtype, Subtype.exists, coe_subtype, injective_subtype, injective_subtype.mem_set_image, map_span, mem_coe, mem_corootSpace, mem_image, mem_map
-/
lemma mem_corootSpace' {x : H} :
    x in corootSpace α ↔
    x in Submodule.span R ({⁅y, z⁆ | (y in rootSpace H α) (z in rootSpace H (-α))} : Set H) := by
  set s : Set H := ({⁅y, z⁆ | (y in rootSpace H α) (z in rootSpace H (-α))} : Set H)
  suffices H.subtype '' s = {⁅y, z⁆ | (y in rootSpace H α) (z in rootSpace H (-α))} by
    erw [← (H : Submodule R L).injective_subtype.mem_set_image (s := Submodule.span R s)]
    rw [mem_image]
    simp_rw [SetLike.mem_coe]
    rw [← Submodule.mem_map]; rw [Submodule.coe_subtype]; rw [Submodule.map_span]; rw [mem_corootSpace]; rw [← this]
  ext u
  simp only [Submodule.coe_subtype, mem_image, Subtype.exists, LieSubalgebra.mem_toSubmodule,
    exists_and_right, exists_eq_right, mem_ofPred_eq, s]
  refine ⟨fun ⟨_, y, hy, z, hz, hyz⟩ => ⟨y, hy, z, hz, hyz⟩,
    fun ⟨y, hy, z, hz, hyz⟩ => ⟨?_, y, hy, z, hz, hyz⟩⟩
  convert!
    (rootSpaceProduct R L H α (-α) 0 (add_neg_cancel α) (⟨y, hy⟩ otimesₜ[R] ⟨z, hz⟩)).property using 0
  simp [hyz]

section FiniteDimensional

variable {K : Type*} [Field K] [LieAlgebra K L]
variable [FiniteDimensional K L] (H : LieSubalgebra K L) [H.IsCartanSubalgebra]
variable [LieModule.IsTriangularizable K H L]

/--
lemma `lieIdeal_eq_iSup_inf_genWeightSpace` / 引理 `lieIdeal_eq_iSup_inf_genWeightSpace`

English:
lemma lieIdeal_eq_iSup_inf_genWeightSpace
  given: (I : LieIdeal K L)
  proof: eq_iSup_inf_genWeightSpace (N := I.restr H)

中文:
引理 lieIdeal_eq_iSup_inf_genWeightSpace
  条件: (I : LieIdeal K L)
  证明: eq_iSup_inf_genWeightSpace (N := I.restr H)

Depends on / 依赖: I.restr, eq_iSup_inf_genWeightSpace
-/
lemma lieIdeal_eq_iSup_inf_genWeightSpace (I : LieIdeal K L) :
    I.restr H = ⨆ χ : Weight K H L, I.restr H ⊓ genWeightSpace L χ :=
  eq_iSup_inf_genWeightSpace (N := I.restr H)

/--
lemma `lieIdeal_eq_inf_cartan_sup_biSup_inf_rootSpace` / 引理 `lieIdeal_eq_inf_cartan_sup_biSup_inf_rootSpace`

English:
lemma lieIdeal_eq_inf_cartan_sup_biSup_inf_rootSpace
  given: (I : LieIdeal K L)
  proof: by
  refine le_antisymm ?_ (sup_le inf_le_left (iSup₂_le fun _ _ => inf_le_left))
  conv_lhs => rw [lieIdeal_eq_iSup_inf_genWeightSpace]
  exact iSup_le fun α => by
    by_cases hα : α.IsZero
    · rw [show genWeightSpace L (α : H -> K) = H.toLieSubmodule by ext; simp [hα.eq]]
      exact le_sup_lef

中文:
引理 lieIdeal_eq_inf_cartan_sup_biSup_inf_rootSpace
  条件: (I : LieIdeal K L)
  证明: by
  refine le_antisymm ?_ (sup_le inf_le_left (iSup₂_le fun _ _ => inf_le_left))
  conv_lhs => rw [lieIdeal_eq_iSup_inf_genWeightSpace]
  exact iSup_le fun α => by
    by_cases hα : α.IsZero
    · rw [show genWeightSpace L (α : H -> K) = H.toLieSubmodule by ext; simp [hα.eq]]
      exact le_sup_lef

Depends on / 依赖: H.toLieSubmodule, IsZero, conv_lhs, genWeightSpace, iSup_le, inf_le_left, le_antisymm, le_rfl, le_sup_left, le_sup_of_le_right, lieIdeal_eq_iSup_inf_genWeightSpace, sup_le, toLieSubmodule
-/
lemma lieIdeal_eq_inf_cartan_sup_biSup_inf_rootSpace (I : LieIdeal K L) :
    I.restr H = (I.restr H ⊓ H.toLieSubmodule) ⊔
      ⨆ α : Weight K H L, ⨆ (_ : α.IsNonZero), I.restr H ⊓ rootSpace H α := by
  refine le_antisymm ?_ (sup_le inf_le_left (iSup₂_le fun _ _ => inf_le_left))
  conv_lhs => rw [lieIdeal_eq_iSup_inf_genWeightSpace]
  exact iSup_le fun α => by
    by_cases hα : α.IsZero
    · rw [show genWeightSpace L (α : H -> K) = H.toLieSubmodule by ext; simp [hα.eq]]
      exact le_sup_left
    · exact le_sup_of_le_right (le_iSup₂_of_le α hα le_rfl)

/--
lemma `cartan_sup_iSup_rootSpace_eq_top` / 引理 `cartan_sup_iSup_rootSpace_eq_top`

English:
lemma cartan_sup_iSup_rootSpace_eq_top
  proof: by
  rw [eq_top_iff]; rw [← LieModule.iSup_genWeightSpace_eq_top']; rw [iSup_le_iff]
  intro α
  by_cases hα : α.IsZero
  · simp [hα]
· exact le_sup_of_le_right le_iSup₂_of_le α hα (le_refl _)

中文:
引理 cartan_sup_iSup_rootSpace_eq_top
  证明: by
  rw [eq_top_iff]; rw [← LieModule.iSup_genWeightSpace_eq_top']; rw [iSup_le_iff]
  intro α
  by_cases hα : α.IsZero
  · simp [hα]
· exact le_sup_of_le_right le_iSup₂_of_le α hα (le_refl _)

Depends on / 依赖: IsZero, LieModule, LieModule.iSup_genWeightSpace_eq_top, eq_top_iff, iSup_genWeightSpace_eq_top, iSup_le_iff, le_refl, le_sup_of_le_right
-/
lemma cartan_sup_iSup_rootSpace_eq_top :
    H.toLieSubmodule ⊔ ⨆ α : Weight K H L, ⨆ (_ : α.IsNonZero), rootSpace H α = ⊤ := by
  rw [eq_top_iff]; rw [← LieModule.iSup_genWeightSpace_eq_top']; rw [iSup_le_iff]
  intro α
  by_cases hα : α.IsZero
  · simp [hα]
· exact le_sup_of_le_right le_iSup₂_of_le α hα (le_refl _)

end FiniteDimensional

end LieAlgebra
