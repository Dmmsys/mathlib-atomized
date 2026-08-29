/-
Copyright (c) 2022 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer, Kevin Klinge, Andrew Yang
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.RingTheory.OreLocalization.NonZeroDivisors

/-!

# Module and Ring instances of Ore Localizations

The `Monoid` and `DistribMulAction` instances and additive versions are provided in
`Mathlib/RingTheory/OreLocalization/Basic.lean`.

-/

@[expose] public section

assert_not_exists Subgroup

universe u

namespace OreLocalization

section Module

variable {R : Type*} [Semiring R] {S : Submonoid R} [OreSet S]
variable {X : Type*} [AddCommMonoid X] [Module R X]

/--
theorem `zero_smul` / 定理 `zero_smul`

English:
theorem zero_smul
  given: (x : X[S⁻¹])
  statement: (0 : R[S⁻¹]) • x = 0
  proof: by
  induction x with | _ r s
  rw [OreLocalization.zero_def]; rw [oreDiv_smul_char 0 r 1 s 0 1 (by simp)]; simp

中文:
定理 zero_smul
  条件: (x : X[S⁻¹])
  结论: (0 : R[S⁻¹]) • x = 0
  证明: by
  induction x with | _ r s
  rw [OreLocalization.zero_def]; rw [oreDiv_smul_char 0 r 1 s 0 1 (by simp)]; simp
-/
protected theorem zero_smul (x : X[S⁻¹]) : (0 : R[S⁻¹]) • x = 0 := by
  induction x with | _ r s
  rw [OreLocalization.zero_def]; rw [oreDiv_smul_char 0 r 1 s 0 1 (by simp)]; simp

/--
theorem `add_smul` / 定理 `add_smul`

English:
theorem add_smul
  given: (y z : R[S⁻¹]) (x : X[S⁻¹])
  proof: by
  induction x with | _ r₁ s₁
  induction y with | _ r₂ s₂
  induction z with | _ r₃ s₃
  rcases oreDivAddChar' r₂ r₃ s₂ s₃ with ⟨ra, sa, ha, q⟩
  rw [q]
  clear q
  rw [OreLocalization.expand' r₂ s₂ sa]
  rcases oreDivSMulChar' (sa • r₂) r₁ (sa * s₂) s₁ with ⟨rb, sb, hb, q⟩
  rw [q]
  clear q
  have hs₃rasb : sb * ra * s₃ in S := by
    rw [mul_assoc]; rw [← ha]
    norm_cast
    apply SetLike.coe_mem
  rw [OreLocalization.expand _ _ _ hs₃rasb]
  have ha' : ↑((sb * sa) * s₂) = sb * ra * s₃ := by simp [ha, mul_assoc]
  rw [← Subtype.coe_eq_of_eq_mk ha']
  rcases oreDivSMulChar' ((sb * ra) • r₃) r₁ (sb * sa * s₂) s₁ with ⟨rc, sc, hc, hc'⟩
  rw [hc']
  rw [oreDiv_add_char _ _ 1 sc (by simp [mul_assoc])]
  rw [OreLocalization.expand' (sa • r₂ + ra • r₃) (sa * s₂) (sc * sb)]
  simp only [smul_eq_mul, one_smul, Submonoid.smul_def, mul_add, Submonoid.coe_mul] at hb hc ⊢
  rw [mul_assoc]; rw [hb]; rw [mul_assoc]; rw [← mul_assoc _ ra]; rw [hc]; rw [← mul_assoc]; rw [← add_mul]
  rw [OreLocalization.smul_cancel']
  simp only [add_smul, ← mul_assoc, smul_smul]

中文:
定理 add_smul
  条件: (y z : R[S⁻¹]) (x : X[S⁻¹])
  证明: by
  induction x with | _ r₁ s₁
  induction y with | _ r₂ s₂
  induction z with | _ r₃ s₃
  rcases oreDivAddChar' r₂ r₃ s₂ s₃ with ⟨ra, sa, ha, q⟩
  rw [q]
  clear q
  rw [OreLocalization.expand' r₂ s₂ sa]
  rcases oreDivSMulChar' (sa • r₂) r₁ (sa * s₂) s₁ with ⟨rb, sb, hb, q⟩
  rw [q]
  clear q
  have hs₃rasb : sb * ra * s₃ in S := by
    rw [mul_assoc]; rw [← ha]
    norm_cast
    apply SetLike.coe_mem
  rw [OreLocalization.expand _ _ _ hs₃rasb]
  have ha' : ↑((sb * sa) * s₂) = sb * ra * s₃ := by simp [ha, mul_assoc]
  rw [← Subtype.coe_eq_of_eq_mk ha']
  rcases oreDivSMulChar' ((sb * ra) • r₃) r₁ (sb * sa * s₂) s₁ with ⟨rc, sc, hc, hc'⟩
  rw [hc']
  rw [oreDiv_add_char _ _ 1 sc (by simp [mul_assoc])]
  rw [OreLocalization.expand' (sa • r₂ + ra • r₃) (sa * s₂) (sc * sb)]
  simp only [smul_eq_mul, one_smul, Submonoid.smul_def, mul_add, Submonoid.coe_mul] at hb hc ⊢
  rw [mul_assoc]; rw [hb]; rw [mul_assoc]; rw [← mul_assoc _ ra]; rw [hc]; rw [← mul_assoc]; rw [← add_mul]
  rw [OreLocalization.smul_cancel']
  simp only [add_smul, ← mul_assoc, smul_smul]
-/
protected theorem add_smul (y z : R[S⁻¹]) (x : X[S⁻¹]) :
    (y + z) • x = y • x + z • x := by
  induction x with | _ r₁ s₁
  induction y with | _ r₂ s₂
  induction z with | _ r₃ s₃
  rcases oreDivAddChar' r₂ r₃ s₂ s₃ with ⟨ra, sa, ha, q⟩
  rw [q]
  clear q
  rw [OreLocalization.expand' r₂ s₂ sa]
  rcases oreDivSMulChar' (sa • r₂) r₁ (sa * s₂) s₁ with ⟨rb, sb, hb, q⟩
  rw [q]
  clear q
  have hs₃rasb : sb * ra * s₃ in S := by
    rw [mul_assoc]; rw [← ha]
    norm_cast
    apply SetLike.coe_mem
  rw [OreLocalization.expand _ _ _ hs₃rasb]
  have ha' : ↑((sb * sa) * s₂) = sb * ra * s₃ := by simp [ha, mul_assoc]
  rw [← Subtype.coe_eq_of_eq_mk ha']
  rcases oreDivSMulChar' ((sb * ra) • r₃) r₁ (sb * sa * s₂) s₁ with ⟨rc, sc, hc, hc'⟩
  rw [hc']
  rw [oreDiv_add_char _ _ 1 sc (by simp [mul_assoc])]
  rw [OreLocalization.expand' (sa • r₂ + ra • r₃) (sa * s₂) (sc * sb)]
  simp only [smul_eq_mul, one_smul, Submonoid.smul_def, mul_add, Submonoid.coe_mul] at hb hc ⊢
  rw [mul_assoc]; rw [hb]; rw [mul_assoc]; rw [← mul_assoc _ ra]; rw [hc]; rw [← mul_assoc]; rw [← add_mul]
  rw [OreLocalization.smul_cancel']
  simp only [add_smul, ← mul_assoc, smul_smul]

end Module

section Semiring

variable {R : Type*} [Semiring R] {S : Submonoid R} [OreSet S]

attribute [local instance] OreLocalization.oreEqv

/--
theorem `left_distrib` / 定理 `left_distrib`

English:
theorem left_distrib
  given: (x y z : R[S⁻¹])
  statement: x * (y + z) = x * y + x * z
  proof: OreLocalization.smul_add _ _ _

中文:
定理 left_distrib
  条件: (x y z : R[S⁻¹])
  结论: x * (y + z) = x * y + x * z
  证明: OreLocalization.smul_add _ _ _
-/
protected theorem left_distrib (x y z : R[S⁻¹]) : x * (y + z) = x * y + x * z :=
  OreLocalization.smul_add _ _ _

/--
theorem `right_distrib` / 定理 `right_distrib`

English:
theorem right_distrib
  given: (x y z : R[S⁻¹])
  statement: (x + y) * z = x * z + y * z
  proof: OreLocalization.add_smul _ _ _

中文:
定理 right_distrib
  条件: (x y z : R[S⁻¹])
  结论: (x + y) * z = x * z + y * z
  证明: OreLocalization.add_smul _ _ _

Depends on / 依赖: OreLocalization, OreLocalization.add_smul, add_smul
-/
theorem right_distrib (x y z : R[S⁻¹]) : (x + y) * z = x * z + y * z :=
  OreLocalization.add_smul _ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Semiring R[S⁻¹]
  body: (inferInstance : MonoidWithZero (R[S⁻¹]))
  __ := (inferInstance : AddCommMonoid (R[S⁻¹]))
  left_distrib := OreLocalization.left_distrib
  right_distrib := right_distrib

中文:
实例 :
  签名: 半环 R[S⁻¹]
  定义体: (inferInstance : MonoidWithZero (R[S⁻¹]))
  __ := (inferInstance : AddCommMonoid (R[S⁻¹]))
  left_distrib := OreLocalization.left_distrib
  right_distrib := right_distrib

Depends on / 依赖: MonoidWithZero
-/
instance : Semiring R[S⁻¹] where
  __ := (inferInstance : MonoidWithZero (R[S⁻¹]))
  __ := (inferInstance : AddCommMonoid (R[S⁻¹]))
  left_distrib := OreLocalization.left_distrib
  right_distrib := right_distrib

variable {X : Type*} [AddCommMonoid X] [Module R X]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module R[S⁻¹] X[S⁻¹]
  body: OreLocalization.add_smul
  zero_smul := OreLocalization.zero_smul

中文:
实例 :
  签名: 模 R[S⁻¹] X[S⁻¹]
  定义体: OreLocalization.add_smul
  zero_smul := OreLocalization.zero_smul

Depends on / 依赖: OreLocalization, OreLocalization.add_smul, add_smul
-/
instance : Module R[S⁻¹] X[S⁻¹] where
  add_smul := OreLocalization.add_smul
  zero_smul := OreLocalization.zero_smul

instance {R₀} [Semiring R₀] [Module R₀ X] [Module R₀ R]
    [IsScalarTower R₀ R X] [IsScalarTower R₀ R R] :
    Module R₀ X[S⁻¹] where
  add_smul r s x := by simp only [← smul_one_oreDiv_one_smul, add_smul, ← add_oreDiv]
  zero_smul x := by rw [← smul_one_oreDiv_one_smul, zero_smul, zero_oreDiv, zero_smul]

@[simp]
/--
lemma `nsmul_eq_nsmul` / 引理 `nsmul_eq_nsmul`

English:
lemma nsmul_eq_nsmul
  given: (n : Nat) (x : X[S⁻¹])
  proof: OreLocalization.instModuleOfIsScalarTower (R₀ := Nat) (R := R) (X := X) (S := S)
    HSMul.hSMul (self := @instHSMul _ _ inst.toSMul) n x = n • x := by
  let inst := OreLocalization.instModuleOfIsScalarTower (R₀ := Nat) (R := R) (X := X) (S := S)
  exact congr($(AddCommMonoid.uniqueNatModule.2 inst).smul n x)

中文:
引理 nsmul_eq_nsmul
  条件: (n : 自然数) (x : X[S⁻¹])
  证明: OreLocalization.instModuleOfIsScalarTower (R₀ := Nat) (R := R) (X := X) (S := S)
    HSMul.hSMul (self := @instHSMul _ _ inst.toSMul) n x = n • x := by
  let inst := OreLocalization.instModuleOfIsScalarTower (R₀ := Nat) (R := R) (X := X) (S := S)
  exact congr($(AddCommMonoid.uniqueNatModule.2 inst).smul n x)

Depends on / 依赖: OreLocalization, OreLocalization.instModuleOfIsScalarTower, instModuleOfIsScalarTower
-/
lemma nsmul_eq_nsmul (n : Nat) (x : X[S⁻¹]) :
    letI inst := OreLocalization.instModuleOfIsScalarTower (R₀ := Nat) (R := R) (X := X) (S := S)
    HSMul.hSMul (self := @instHSMul _ _ inst.toSMul) n x = n • x := by
  let inst := OreLocalization.instModuleOfIsScalarTower (R₀ := Nat) (R := R) (X := X) (S := S)
  exact congr($(AddCommMonoid.uniqueNatModule.2 inst).smul n x)

/-- The ring homomorphism from `R` to `R[S⁻¹]`, mapping `r : R` to the fraction `r /ₒ 1`. -/
@[simps!]
/--
Definition of `numeratorRingHom` / `numeratorRingHom` 的定义

English:
abbreviation numeratorRingHom
  signature: : R ->+* R[S⁻¹] where
  body: numeratorHom
  map_zero' := by with_unfolding_all exact OreLocalization.zero_def
  map_add' _ _ := add_oreDiv.symm

中文:
缩写 numeratorRingHom
  签名: : R ->+* R[S⁻¹] where
  定义体: numeratorHom
  map_zero' := by with_unfolding_all exact OreLocalization.zero_def
  map_add' _ _ := add_oreDiv.symm

Depends on / 依赖: numeratorHom
-/
abbrev numeratorRingHom : R ->+* R[S⁻¹] where
  __ := numeratorHom
  map_zero' := by with_unfolding_all exact OreLocalization.zero_def
  map_add' _ _ := add_oreDiv.symm

instance {R₀} [CommSemiring R₀] [Algebra R₀ R] : Algebra R₀ R[S⁻¹] where
  __ := (inferInstance : Module R₀ R[S⁻¹])
  algebraMap := numeratorRingHom.comp (algebraMap R₀ R)
  commutes' r x := by
    induction x using OreLocalization.ind with | _ r₁ s₁
    dsimp
    rw [mul_div_one]; rw [oreDiv_mul_char _ _ _ _ (algebraMap R₀ R r) s₁ (Algebra.commutes _ _).symm]; rw [Algebra.commutes]; rw [mul_one]
  smul_def' r x := by
    dsimp
    rw [Algebra.algebraMap_eq_smul_one]; rw [← smul_eq_mul]; rw [smul_one_oreDiv_one_smul]

section UMP

variable {T : Type*} [Semiring T]
variable (f : R ->+* T) (fS : S ->* Units T)
variable (hf : forall s : S, f s = fS s)

/--
Definition of `universalHom` / `universalHom` 的定义

English:
definition universalHom
  signature: : R[S⁻¹] ->+* T
  body: { universalMulHom f.toMonoidHom fS hf with
    map_zero' := by
      simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe]
      rw [OreLocalization.zero_def]; rw [universalMulHom_apply]
      simp
    map_add' := fun x y => by
      simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe]
      induction x with | _ r₁ s₁
      induction y with | _ r₂ s₂
      rcases oreDivAddChar' r₁ r₂ s₁ s₂ with ⟨r₃, s₃, h₃, h₃'⟩
      rw [h₃']
      clear h₃'
      simp only [smul_eq_mul, universalMulHom_apply, MonoidHom.coe_coe,
        Submonoid.smul_def]
      simp only [mul_inv_rev, map_mul, map_add, map_mul, Units.val_mul]
      rw [mul_add]; rw [mul_assoc]; rw [← mul_assoc _ (f s₃)]; rw [hf]; rw [← Units.val_mul]
      simp only [one_mul, inv_mul_cancel, Units.val_one]
      congr 1
      rw [← mul_assoc]
      congr 1
      norm_cast at h₃
      have h₃' := Subtype.coe_eq_of_eq_mk h₃
      rw [← Units.val_mul]; rw [← mul_inv_rev]; rw [← fS.map_mul]; rw [h₃']
      rw [Units.inv_mul_eq_iff_eq_mul]; rw [Units.eq_mul_inv_iff_mul_eq]; rw [← hf]; rw [← hf]
      simp only [map_mul] }

中文:
定义 universalHom
  签名: : R[S⁻¹] ->+* T
  定义体: { universalMulHom f.toMonoidHom fS hf with
    map_zero' := by
      simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe]
      rw [OreLocalization.zero_def]; rw [universalMulHom_apply]
      simp
    map_add' := fun x y => by
      simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe]
      induction x with | _ r₁ s₁
      induction y with | _ r₂ s₂
      rcases oreDivAddChar' r₁ r₂ s₁ s₂ with ⟨r₃, s₃, h₃, h₃'⟩
      rw [h₃']
      clear h₃'
      simp only [smul_eq_mul, universalMulHom_apply, MonoidHom.coe_coe,
        Submonoid.smul_def]
      simp only [mul_inv_rev, map_mul, map_add, map_mul, Units.val_mul]
      rw [mul_add]; rw [mul_assoc]; rw [← mul_assoc _ (f s₃)]; rw [hf]; rw [← Units.val_mul]
      simp only [one_mul, inv_mul_cancel, Units.val_one]
      congr 1
      rw [← mul_assoc]
      congr 1
      norm_cast at h₃
      have h₃' := Subtype.coe_eq_of_eq_mk h₃
      rw [← Units.val_mul]; rw [← mul_inv_rev]; rw [← fS.map_mul]; rw [h₃']
      rw [Units.inv_mul_eq_iff_eq_mul]; rw [Units.eq_mul_inv_iff_mul_eq]; rw [← hf]; rw [← hf]
      simp only [map_mul] }

Depends on / 依赖: MonoidH, MonoidHom, MonoidHom.toOneHom_coe, OneHom, OneHom.toFun_eq_coe, OreLocalization, OreLocalization.zero_def, RingHom, RingHom.toMonoidHom_eq_coe, f.toMonoidHom, map_add, map_zero, oreDivAddChar, smul_eq_mul, toFun_eq_coe, toMonoidHom, toMonoidHom_eq_coe, toOneHom_coe, universalMulHom, universalMulHom_apply
-/
def universalHom : R[S⁻¹] ->+* T :=
  { universalMulHom f.toMonoidHom fS hf with
    map_zero' := by
      simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe]
      rw [OreLocalization.zero_def]; rw [universalMulHom_apply]
      simp
    map_add' := fun x y => by
      simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe]
      induction x with | _ r₁ s₁
      induction y with | _ r₂ s₂
      rcases oreDivAddChar' r₁ r₂ s₁ s₂ with ⟨r₃, s₃, h₃, h₃'⟩
      rw [h₃']
      clear h₃'
      simp only [smul_eq_mul, universalMulHom_apply, MonoidHom.coe_coe,
        Submonoid.smul_def]
      simp only [mul_inv_rev, map_mul, map_add, map_mul, Units.val_mul]
      rw [mul_add]; rw [mul_assoc]; rw [← mul_assoc _ (f s₃)]; rw [hf]; rw [← Units.val_mul]
      simp only [one_mul, inv_mul_cancel, Units.val_one]
      congr 1
      rw [← mul_assoc]
      congr 1
      norm_cast at h₃
      have h₃' := Subtype.coe_eq_of_eq_mk h₃
      rw [← Units.val_mul]; rw [← mul_inv_rev]; rw [← fS.map_mul]; rw [h₃']
      rw [Units.inv_mul_eq_iff_eq_mul]; rw [Units.eq_mul_inv_iff_mul_eq]; rw [← hf]; rw [← hf]
      simp only [map_mul] }

/--
theorem `universalHom_apply` / 定理 `universalHom_apply`

English:
theorem universalHom_apply
  given: {r : R} {s : S}
  proof: rfl

中文:
定理 universalHom_apply
  条件: {r : R} {s : S}
  证明: rfl
-/
theorem universalHom_apply {r : R} {s : S} :
    universalHom f fS hf (r /ₒ s) = ((fS s)⁻¹ : Units T) * f r :=
  rfl

/--
theorem `universalHom_commutes` / 定理 `universalHom_commutes`

English:
theorem universalHom_commutes
  given: {r : R}
  statement: universalHom f fS hf (numeratorHom r) = f r
  proof: by
  simp [numeratorHom_apply, universalHom_apply]

中文:
定理 universalHom_commutes
  条件: {r : R}
  结论: universalHom f fS hf (numeratorHom r) = f r
  证明: by
  simp [numeratorHom_apply, universalHom_apply]

Depends on / 依赖: numeratorHom_apply, universalHom_apply
-/
theorem universalHom_commutes {r : R} : universalHom f fS hf (numeratorHom r) = f r := by
  simp [numeratorHom_apply, universalHom_apply]

/--
theorem `universalHom_unique` / 定理 `universalHom_unique`

English:
theorem universalHom_unique
  given: (φ : R[S⁻¹] ->+* T) (huniv : forall r : R, φ (numeratorHom r) = f r)
  proof: RingHom.coe_monoidHom_injective universalMulHom_unique (RingHom.toMonoidHom f) fS hf (↑φ) huniv

中文:
定理 universalHom_unique
  条件: (φ : R[S⁻¹] ->+* T) (huniv : 对任意 r : R, φ (numeratorHom r) = f r)
  证明: RingHom.coe_monoidHom_injective universalMulHom_unique (RingHom.toMonoidHom f) fS hf (↑φ) huniv

Depends on / 依赖: RingHom, RingHom.coe_monoidHom_injective, RingHom.toMonoidHom, coe_monoidHom_injective, toMonoidHom, universalMulHom_unique
-/
theorem universalHom_unique (φ : R[S⁻¹] ->+* T) (huniv : forall r : R, φ (numeratorHom r) = f r) :
    φ = universalHom f fS hf :=
RingHom.coe_monoidHom_injective universalMulHom_unique (RingHom.toMonoidHom f) fS hf (↑φ) huniv

end UMP

end Semiring

section Ring

variable {R : Type*} [Ring R] {S : Submonoid R} [OreSet S]
variable {X : Type*} [AddCommGroup X] [Module R X]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Ring R[S⁻¹]
  body: (inferInstance : Semiring R[S⁻¹])
  __ := (inferInstance : AddGroup R[S⁻¹])

@[simp]

中文:
实例 :
  签名: 环 R[S⁻¹]
  定义体: (inferInstance : Semiring R[S⁻¹])
  __ := (inferInstance : AddGroup R[S⁻¹])

@[simp]

Depends on / 依赖: Semiring
-/
instance : Ring R[S⁻¹] where
  __ := (inferInstance : Semiring R[S⁻¹])
  __ := (inferInstance : AddGroup R[S⁻¹])

@[simp]
/--
lemma `zsmul_eq_zsmul` / 引理 `zsmul_eq_zsmul`

English:
lemma zsmul_eq_zsmul
  given: (n : Int) (x : X[S⁻¹])
  proof: OreLocalization.instModuleOfIsScalarTower (R₀ := Int) (R := R) (X := X) (S := S)
    HSMul.hSMul (self := @instHSMul _ _ inst.toSMul) n x = n • x := by
  let inst := OreLocalization.instModuleOfIsScalarTower (R₀ := Int) (R := R) (X := X) (S := S)
  exact congr($(AddCommGroup.uniqueIntModule.2 inst).smul n x)

中文:
引理 zsmul_eq_zsmul
  条件: (n : 整数) (x : X[S⁻¹])
  证明: OreLocalization.instModuleOfIsScalarTower (R₀ := Int) (R := R) (X := X) (S := S)
    HSMul.hSMul (self := @instHSMul _ _ inst.toSMul) n x = n • x := by
  let inst := OreLocalization.instModuleOfIsScalarTower (R₀ := Int) (R := R) (X := X) (S := S)
  exact congr($(AddCommGroup.uniqueIntModule.2 inst).smul n x)

Depends on / 依赖: OreLocalization, OreLocalization.instModuleOfIsScalarTower, instModuleOfIsScalarTower
-/
lemma zsmul_eq_zsmul (n : Int) (x : X[S⁻¹]) :
    letI inst := OreLocalization.instModuleOfIsScalarTower (R₀ := Int) (R := R) (X := X) (S := S)
    HSMul.hSMul (self := @instHSMul _ _ inst.toSMul) n x = n • x := by
  let inst := OreLocalization.instModuleOfIsScalarTower (R₀ := Int) (R := R) (X := X) (S := S)
  exact congr($(AddCommGroup.uniqueIntModule.2 inst).smul n x)

open nonZeroDivisors

/--
theorem `numeratorHom_inj` / 定理 `numeratorHom_inj`

English:
theorem numeratorHom_inj
  given: (hS : S <= nonZeroDivisorsLeft R)
  proof: fun r₁ r₂ h => by
  rw [numeratorHom_apply]; rw [numeratorHom_apply]; rw [oreDiv_eq_iff] at h
  rcases h with ⟨u, v, h₁, h₂⟩
  simp only [S.coe_one, mul_one, Submonoid.smul_def, smul_eq_mul] at h₁ h₂
  rw [← h₂]; rw [← sub_eq_zero]; rw [← mul_sub] at h₁
  exact (sub_eq_zero.mp (hS u.2 _ h₁)).symm

中文:
定理 numeratorHom_inj
  条件: (hS : S <= nonZeroDivisorsLeft R)
  证明: fun r₁ r₂ h => by
  rw [numeratorHom_apply]; rw [numeratorHom_apply]; rw [oreDiv_eq_iff] at h
  rcases h with ⟨u, v, h₁, h₂⟩
  simp only [S.coe_one, mul_one, Submonoid.smul_def, smul_eq_mul] at h₁ h₂
  rw [← h₂]; rw [← sub_eq_zero]; rw [← mul_sub] at h₁
  exact (sub_eq_zero.mp (hS u.2 _ h₁)).symm

Depends on / 依赖: S.coe_one, Submonoid, Submonoid.smul_def, coe_one, mul_one, mul_sub, numeratorHom_apply, oreDiv_eq_iff, smul_def, smul_eq_mul, sub_eq_zero, sub_eq_zero.mp
-/
theorem numeratorHom_inj (hS : S <= nonZeroDivisorsLeft R) :
    Function.Injective (numeratorHom : R -> R[S⁻¹]) :=
  fun r₁ r₂ h => by
  rw [numeratorHom_apply]; rw [numeratorHom_apply]; rw [oreDiv_eq_iff] at h
  rcases h with ⟨u, v, h₁, h₂⟩
  simp only [S.coe_one, mul_one, Submonoid.smul_def, smul_eq_mul] at h₁ h₂
  rw [← h₂]; rw [← sub_eq_zero]; rw [← mul_sub] at h₁
  exact (sub_eq_zero.mp (hS u.2 _ h₁)).symm

end Ring

noncomputable section DivisionRing

open nonZeroDivisors

variable {R : Type*} [Ring R] [Nontrivial R] [NoZeroDivisors R] [OreSet R⁰]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DivisionRing R[R⁰⁻¹]
  body: OreLocalization.mul_inv_cancel
  inv_zero := OreLocalization.inv_zero
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

中文:
实例 :
  签名: 除环 R[R⁰⁻¹]
  定义体: OreLocalization.mul_inv_cancel
  inv_zero := OreLocalization.inv_zero
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

Depends on / 依赖: OreLocalization, OreLocalization.mul_inv_cancel, mul_inv_cancel
-/
instance : DivisionRing R[R⁰⁻¹] where
  mul_inv_cancel := OreLocalization.mul_inv_cancel
  inv_zero := OreLocalization.inv_zero
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

end DivisionRing

section CommSemiring

variable {R : Type*} [CommSemiring R] {S : Submonoid R} [OreSet S]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommSemiring R[S⁻¹]
  body: (inferInstance : Semiring R[S⁻¹])
  __ := (inferInstance : CommMonoid R[S⁻¹])

中文:
实例 :
  签名: 交换半环 R[S⁻¹]
  定义体: (inferInstance : Semiring R[S⁻¹])
  __ := (inferInstance : CommMonoid R[S⁻¹])

Depends on / 依赖: Semiring
-/
instance : CommSemiring R[S⁻¹] where
  __ := (inferInstance : Semiring R[S⁻¹])
  __ := (inferInstance : CommMonoid R[S⁻¹])

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R] {S : Submonoid R} [OreSet S]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommRing R[S⁻¹]
  body: (inferInstance : Ring R[S⁻¹])
  __ := (inferInstance : CommMonoid R[S⁻¹])

中文:
实例 :
  签名: 交换环 R[S⁻¹]
  定义体: (inferInstance : Ring R[S⁻¹])
  __ := (inferInstance : CommMonoid R[S⁻¹])
-/
instance : CommRing R[S⁻¹] where
  __ := (inferInstance : Ring R[S⁻¹])
  __ := (inferInstance : CommMonoid R[S⁻¹])

end CommRing

section Field

open nonZeroDivisors

variable {R : Type*} [CommRing R] [Nontrivial R] [NoZeroDivisors R] [OreSet R⁰]

noncomputable
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Field R[R⁰⁻¹]
  body: (inferInstance : DivisionRing R[R⁰⁻¹])
  __ := (inferInstance : CommMonoid R[R⁰⁻¹])

中文:
实例 :
  签名: 域 R[R⁰⁻¹]
  定义体: (inferInstance : DivisionRing R[R⁰⁻¹])
  __ := (inferInstance : CommMonoid R[R⁰⁻¹])

Depends on / 依赖: DivisionRing
-/
instance : Field R[R⁰⁻¹] where
  __ := (inferInstance : DivisionRing R[R⁰⁻¹])
  __ := (inferInstance : CommMonoid R[R⁰⁻¹])

end Field

end OreLocalization
