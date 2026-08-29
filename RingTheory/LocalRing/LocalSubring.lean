/-
Copyright (c) 2024 Andrew Yang, Yaël Dillies, Javier López-Contreras. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Yaël Dillies, Javier López-Contreras
-/
module

public import Mathlib.Tactic.FieldSimp
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Local subrings of fields

## Main results
- `LocalSubring` : The class of local subrings of a commutative ring.
- `LocalSubring.ofPrime`: The localization of a subring as a `LocalSubring`.
-/

@[expose] public section

open IsLocalRing Set

variable {R S : Type*} [CommRing R] [CommRing S]
variable {K : Type*} [Field K]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nontrivial
  signature: S] (f
  body: .of_surjective' (f.restrict s _ (fun _ => Set.mem_image_of_mem f))
    (fun ⟨_, a, ha, e⟩ => ⟨⟨a, ha⟩, Subtype.ext e⟩)

中文:
实例 [非平凡
  签名: S] (f
  定义体: .of_surjective' (f.restrict s _ (fun _ => Set.mem_image_of_mem f))
    (fun ⟨_, a, ha, e⟩ => ⟨⟨a, ha⟩, Subtype.ext e⟩)

Depends on / 依赖: Set.mem_image_of_mem, Subtype, Subtype.ext, f.restrict, mem_image_of_mem, of_surjective, restrict
-/
instance [Nontrivial S] (f : R ->+* S) (s : Subring R) [IsLocalRing s] : IsLocalRing (s.map f) :=
  .of_surjective' (f.restrict s _ (fun _ => Set.mem_image_of_mem f))
    (fun ⟨_, a, ha, e⟩ => ⟨⟨a, ha⟩, Subtype.ext e⟩)

/--
Instance `isLocalRing_top` / 实例 `isLocalRing_top`

English:
instance isLocalRing_top
  signature: [IsLocalRing R]
  body: Subring.topEquiv.symm.isLocalRing

中文:
实例 isLocalRing_top
  签名: [是局部环 R]
  定义体: Subring.topEquiv.symm.isLocalRing

Depends on / 依赖: Subring, Subring.topEquiv.symm.isLocalRing, isLocalRing, topEquiv
-/
instance isLocalRing_top [IsLocalRing R] : IsLocalRing (⊤ : Subring R) :=
  Subring.topEquiv.symm.isLocalRing

variable (R) in
/-- The class of local subrings of a commutative ring. -/
@[ext]
/--
Definition of `LocalSubring` / `LocalSubring` 的定义

English:
structure LocalSubring
  parameters: where
  axioms and operations (2):
    - toSubring : Subring R
    - [isLocalRing : IsLocalRing toSubring]

中文:
结构 Local子环
  参数: where
  公理与运算 (2 个):
    - toSubring : 子环 R
    - [isLocalRing : 是局部环 toSubring]

Depends on / 依赖: mul_comm
-/
structure LocalSubring where
  /-- The underlying subring of a local subring. -/
  toSubring : Subring R
  [isLocalRing : IsLocalRing toSubring]

namespace LocalSubring

attribute [instance] isLocalRing

/--
lemma `toSubring_injective` / 引理 `toSubring_injective`

English:
lemma toSubring_injective
  statement: Function.Injective (toSubring (R := R))
  proof: by
  rintro ⟨a, b⟩ ⟨c, d⟩ rfl; rfl

中文:
引理 toSubring_injective
  结论: 函数.单射 (toSubring (R := R))
  证明: by
  rintro ⟨a, b⟩ ⟨c, d⟩ rfl; rfl

Depends on / 依赖: completeSpace_coe, isClosed_closure, isClosed_closure.completeSpace_coe
-/
lemma toSubring_injective : Function.Injective (toSubring (R := R)) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ rfl; rfl

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (S : LocalSubring R) (s : Set R) (hs : s = ↑S.toSubring)
  body: LocalSubring.mk (S.toSubring.copy s hs) (isLocalRing := hs ▸ S.2)

中文:
定义 copy
  签名: (S : Local子环 R) (s : 集合 R) (hs : s = ↑S.toSubring)
  定义体: LocalSubring.mk (S.toSubring.copy s hs) (isLocalRing := hs ▸ S.2)
-/
protected def copy (S : LocalSubring R) (s : Set R) (hs : s = ↑S.toSubring) : LocalSubring R :=
  LocalSubring.mk (S.toSubring.copy s hs) (isLocalRing := hs ▸ S.2)

/-- The image of a `LocalSubring` as a `LocalSubring`. -/
@[simps! toSubring]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: [Nontrivial S] (f : R ->+* S) (s : LocalSubring R)
  body: mk (s.1.map f)

中文:
定义 map
  签名: [非平凡 S] (f : R ->+* S) (s : Local子环 R)
  定义体: mk (s.1.map f)
-/
def map [Nontrivial S] (f : R ->+* S) (s : LocalSubring R) : LocalSubring S :=
  mk (s.1.map f)

/-- The range of a ring homomorphism from a local ring as a `LocalSubring`. -/
@[simps! toSubring]
/--
Definition of `range` / `range` 的定义

English:
definition range
  signature: [IsLocalRing R] [Nontrivial S] (f : R ->+* S)
  body: .copy (map f (mk ⊤)) f.range (by ext x; exact congr(x in $(Set.image_univ.symm)))

中文:
定义 range
  签名: [是局部环 R] [非平凡 S] (f : R ->+* S)
  定义体: .copy (map f (mk ⊤)) f.range (by ext x; exact congr(x in $(Set.image_univ.symm)))

Depends on / 依赖: Set.image_univ.symm, f.range, image_univ
-/
def range [IsLocalRing R] [Nontrivial S] (f : R ->+* S) : LocalSubring S :=
  .copy (map f (mk ⊤)) f.range (by ext x; exact congr(x in $(Set.image_univ.symm)))

/--
The domination order on local subrings.
`A` dominates `B` if and only if `B ≤ A` (as subrings) and `m_A ∩ B = m_B`.
-/
@[stacks 00I9]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (LocalSubring R)
  body: exists h : A.1 <= B.1, IsLocalHom (Subring.inclusion h)
  le_refl a := ⟨le_rfl, ⟨fun _ => id⟩⟩
  le_trans A B C h₁ h₂ := ⟨h₁.1.trans h₂.1, @RingHom.isLocalHom_comp _ _ _ _ _ _ _ _ h₂.2 h₁.2⟩
  le_antisymm A B h₁ h₂ := toSubring_injective (le_antisymm h₁.1 h₂.1)

中文:
实例 :
  签名: 偏序 (Local子环 R)
  定义体: exists h : A.1 <= B.1, IsLocalHom (Subring.inclusion h)
  le_refl a := ⟨le_rfl, ⟨fun _ => id⟩⟩
  le_trans A B C h₁ h₂ := ⟨h₁.1.trans h₂.1, @RingHom.isLocalHom_comp _ _ _ _ _ _ _ _ h₂.2 h₁.2⟩
  le_antisymm A B h₁ h₂ := toSubring_injective (le_antisymm h₁.1 h₂.1)

Depends on / 依赖: IsLocalHom, Subring, Subring.inclusion, inclusion
-/
instance : PartialOrder (LocalSubring R) where
  le A B := exists h : A.1 <= B.1, IsLocalHom (Subring.inclusion h)
  le_refl a := ⟨le_rfl, ⟨fun _ => id⟩⟩
  le_trans A B C h₁ h₂ := ⟨h₁.1.trans h₂.1, @RingHom.isLocalHom_comp _ _ _ _ _ _ _ _ h₂.2 h₁.2⟩
  le_antisymm A B h₁ h₂ := toSubring_injective (le_antisymm h₁.1 h₂.1)

/--
lemma `le_def` / 引理 `le_def`

English:
lemma le_def
  given: {A B : LocalSubring R}
  proof: Iff.rfl

中文:
引理 le_def
  条件: {A B : Local子环 R}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma le_def {A B : LocalSubring R} :
    A <= B ↔ exists h : A.toSubring <= B.toSubring, IsLocalHom (Subring.inclusion h) := Iff.rfl

/--
lemma `toSubring_mono` / 引理 `toSubring_mono`

English:
lemma toSubring_mono
  statement: Monotone (toSubring (R := R))
  proof: fun _ _ e => e.1

中文:
引理 toSubring_mono
  结论: 递增 (toSubring (R := R))
  证明: fun _ _ e => e.1
-/
lemma toSubring_mono : Monotone (toSubring (R := R)) :=
  fun _ _ e => e.1

section ofPrime

variable (A : Subring K) (P : Ideal A) [P.IsPrime]

set_option backward.isDefEq.respectTransparency false in
/-- The localization of a subring at a prime, as a local subring.
Also see `Localization.subalgebra.ofField` -/
noncomputable
/--
Definition of `ofPrime` / `ofPrime` 的定义

English:
definition ofPrime
  signature: (A : Subring K) (P : Ideal A) [P.IsPrime]
  body: range (IsLocalization.lift (M := P.primeCompl) (S := Localization.AtPrime P)
    (g := A.subtype) (by simp [Ideal.primeCompl, not_imp_not]))

中文:
定义 ofPrime
  签名: (A : 子环 K) (P : 理想 A) [P.是素]
  定义体: range (IsLocalization.lift (M := P.primeCompl) (S := Localization.AtPrime P)
    (g := A.subtype) (by simp [Ideal.primeCompl, not_imp_not]))

Depends on / 依赖: A.subtype, AtPrime, Ideal.primeCompl, IsLocalization, IsLocalization.lift, Localization, Localization.AtPrime, P.primeCompl, not_imp_not, primeCompl, subtype
-/
def ofPrime (A : Subring K) (P : Ideal A) [P.IsPrime] : LocalSubring K :=
  range (IsLocalization.lift (M := P.primeCompl) (S := Localization.AtPrime P)
    (g := A.subtype) (by simp [Ideal.primeCompl, not_imp_not]))

/--
lemma `le_ofPrime` / 引理 `le_ofPrime`

English:
lemma le_ofPrime
  statement: A <= (ofPrime A P).toSubring
  proof: by
  intro x hx
  exact ⟨algebraMap A _ ⟨x, hx⟩, by simp⟩

noncomputable

中文:
引理 le_ofPrime
  结论: A <= (ofPrime A P).toSubring
  证明: by
  intro x hx
  exact ⟨algebraMap A _ ⟨x, hx⟩, by simp⟩

noncomputable

Depends on / 依赖: algebraMap
-/
lemma le_ofPrime : A <= (ofPrime A P).toSubring := by
  intro x hx
  exact ⟨algebraMap A _ ⟨x, hx⟩, by simp⟩

noncomputable
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra A (ofPrime A P).toSubring
  body: (Subring.inclusion (le_ofPrime A P)).toAlgebra

中文:
实例 :
  签名: 代数 A (ofPrime A P).toSubring
  定义体: (Subring.inclusion (le_ofPrime A P)).toAlgebra

Depends on / 依赖: Subring, Subring.inclusion, inclusion, le_ofPrime, toAlgebra
-/
instance : Algebra A (ofPrime A P).toSubring := (Subring.inclusion (le_ofPrime A P)).toAlgebra

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsScalarTower A (ofPrime A P).toSubring K
  body: .of_algebraMap_eq (fun _ => rfl)

中文:
实例 :
  签名: 标量塔 A (ofPrime A P).toSubring K
  定义体: .of_algebraMap_eq (fun _ => rfl)

Depends on / 依赖: of_algebraMap_eq
-/
instance : IsScalarTower A (ofPrime A P).toSubring K := .of_algebraMap_eq (fun _ => rfl)

set_option backward.isDefEq.respectTransparency false in
-- see https://github.com/leanprover-community/mathlib4/issues/29041
set_option linter.unusedSimpArgs false in
/-- The localization of a subring at a prime is indeed isomorphic to its abstract localization. -/
noncomputable
/--
Definition of `ofPrimeEquiv` / `ofPrimeEquiv` 的定义

English:
definition ofPrimeEquiv
  signature: : Localization.AtPrime P ≃ₐ[A] (ofPrime A P).toSubring
  body: by
  refine AlgEquiv.ofInjective (IsLocalization.liftAlgHom (M := P.primeCompl)
    (S := Localization.AtPrime P) (f := Algebra.ofId A K) _) ?_
  intro x y e
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq P.primeCompl x
  obtain ⟨y, t, rfl⟩ := IsLocalization.exists_mk'_eq P.primeCompl y
  have

中文:
定义 ofPrimeEquiv
  签名: : Localization.AtPrime P ≃ₐ[A] (ofPrime A P).toSubring
  定义体: by
  refine AlgEquiv.ofInjective (IsLocalization.liftAlgHom (M := P.primeCompl)
    (S := Localization.AtPrime P) (f := Algebra.ofId A K) _) ?_
  intro x y e
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq P.primeCompl x
  obtain ⟨y, t, rfl⟩ := IsLocalization.exists_mk'_eq P.primeCompl y
  have

Depends on / 依赖: AlgEquiv, AlgEquiv.ofInjective, Algebra, Algebra.algebraMap_ofSubsemiring_apply, Algebra.ofId, Algebra.ofId_apply, AtPrime, IsLocalization, IsLocalization.exists_mk, IsLocalization.liftAlgHom, IsLocalization.lift_mk, IsUnit, Localization, Localization.AtPrime, P.primeCompl, algebraMap_ofSubsemiring_apply, exists_mk, liftAlgHom, lift_mk, ofId_apply
-/
def ofPrimeEquiv : Localization.AtPrime P ≃ₐ[A] (ofPrime A P).toSubring := by
  refine AlgEquiv.ofInjective (IsLocalization.liftAlgHom (M := P.primeCompl)
    (S := Localization.AtPrime P) (f := Algebra.ofId A K) _) ?_
  intro x y e
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq P.primeCompl x
  obtain ⟨y, t, rfl⟩ := IsLocalization.exists_mk'_eq P.primeCompl y
  have H : forall x : P.primeCompl, x.1 != 0 := by rintro ⟨x, hx⟩ rfl; aesop
  have : x.1 = y.1 * t.1.1⁻¹ * s.1.1 := by
    simpa [IsLocalization.lift_mk', Algebra.ofId_apply, H,
Algebra.algebraMap_ofSubsemiring_apply, IsUnit.coe_liftRight] using congr( e * s.1.1)
  rw [IsLocalization.mk'_eq_iff_eq]
  congr 1
  ext
  simp [field, H t, this, mul_comm]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsLocalization.AtPrime (ofPrime A P).toSubring P
  body: IsLocalization.isLocalization_of_algEquiv _ (ofPrimeEquiv A P)

中文:
实例 :
  签名: 是Localization.AtPrime (ofPrime A P).toSubring P
  定义体: IsLocalization.isLocalization_of_algEquiv _ (ofPrimeEquiv A P)

Depends on / 依赖: IsLocalization, IsLocalization.isLocalization_of_algEquiv, isLocalization_of_algEquiv, ofPrimeEquiv
-/
instance : IsLocalization.AtPrime (ofPrime A P).toSubring P :=
  IsLocalization.isLocalization_of_algEquiv _ (ofPrimeEquiv A P)

end ofPrime

end LocalSubring
