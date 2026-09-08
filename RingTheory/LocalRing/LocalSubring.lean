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

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nontrivial S] (f : R →+* S) (s : Subring R) [IsLocalRing s] : IsLocalRing (s.map f) :=
  .of_surjective' (f.restrict s _ (fun _ ↦ Set.mem_image_of_mem f))
    (fun ⟨_, a, ha, e⟩ ↦ ⟨⟨a, ha⟩, Subtype.ext e⟩)
/-
**isLocalRing_top** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：isLocalRing_top [IsLocalRing R] : IsLocalRing (⊤ : Subring R)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquiv.isLocalRing`：∀ {A : Type u_4} {B : Type u_5} [inst : CommSemir
ing A] [IsLocalRing A] [inst_2 : Semiring B] (e : A ≃+* B),   IsLocalRing B
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
-/
instance isLocalRing_top [IsLocalRing R] : IsLocalRing (⊤ : Subring R) :=
  Subring.topEquiv.symm.isLocalRing

variable (R) in
/-- The class of local subrings of a commutative ring. -/
@[ext]
/-
**LocalSubring** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) → [CommRing R] → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The class of local subrings of a commutative ring.
-/
structure LocalSubring where
  /-- The underlying subring of a local subring. -/
  toSubring : Subring R
  [isLocalRing : IsLocalRing toSubring]

namespace LocalSubring

attribute [instance] isLocalRing

/-
**LocalSubring.toSubring_injective** 是 Mathlib 中的一个引理，位于命名空间 `LocalSubring`。
形式化陈述：toSubring_injective : Function.Injective (toSubring (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
-/
lemma toSubring_injective : Function.Injective (toSubring (R := R)) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ rfl; rfl

/-- Copy of a local subring with a new `carrier` equal to the old one.
Useful to fix definitional equalities. -/
/-
**LocalSubring.copy** 是 Mathlib 中的一个定义，位于命名空间 `LocalSubring`。
形式化陈述：{R : Type u_1} → [inst : CommRing R] → (S : LocalSubring R) → (s : Set R) 
→ s = ↑S.toSubring → LocalSubring R
参数：S : LocalSubring R；s : Set R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a local subring with a new `carrier` equal to the old one.
Useful to fix definitional equalities.
-/
protected def copy (S : LocalSubring R) (s : Set R) (hs : s = ↑S.toSubring) : LocalSubring R :=
  LocalSubring.mk (S.toSubring.copy s hs) (isLocalRing := hs ▸ S.2)

/-- The image of a `LocalSubring` as a `LocalSubring`. -/
@[simps! toSubring]
/-
**LocalSubring.map** 是 Mathlib 中的一个定义，位于命名空间 `LocalSubring`。
形式化陈述：map [Nontrivial S] (f : R ->+* S) (s : LocalSubring R) : LocalSubring S
参数：f : R ->+* S；s : LocalSubring R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of a `LocalSubring` as a `LocalSubring`.
-/
def map [Nontrivial S] (f : R →+* S) (s : LocalSubring R) : LocalSubring S :=
  mk (s.1.map f)

/-- The range of a ring homomorphism from a local ring as a `LocalSubring`. -/
@[simps! toSubring]
/-
**LocalSubring.range** 是 Mathlib 中的一个定义，位于命名空间 `LocalSubring`。
形式化陈述：range [IsLocalRing R] [Nontrivial S] (f : R ->+* S) : LocalSubring S
参数：f : R ->+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The range of a ring homomorphism from a local ring as a `LocalSubring`.
-/
def range [IsLocalRing R] [Nontrivial S] (f : R →+* S) : LocalSubring S :=
  .copy (map f (mk ⊤)) f.range (by ext x; exact congr(x ∈ $(Set.image_univ.symm)))

/--
The domination order on local subrings.
`A` dominates `B` if and only if `B ≤ A` (as subrings) and `m_A ∩ B = m_B`.
-/
@[stacks 00I9]
/-
**LocalSubring.** 是 Mathlib 中的一个实例，位于命名空间 `LocalSubring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The domination order on local subrings.
`A` dominates `B` if and only if `B ≤ A` (as subrings) and `m_A ∩ B = m_B`.
-/
instance : PartialOrder (LocalSubring R) where
  le A B := ∃ h : A.1 ≤ B.1, IsLocalHom (Subring.inclusion h)
  le_refl a := ⟨le_rfl, ⟨fun _ ↦ id⟩⟩
  le_trans A B C h₁ h₂ := ⟨h₁.1.trans h₂.1, @RingHom.isLocalHom_comp _ _ _ _ _ _ _ _ h₂.2 h₁.2⟩
  le_antisymm A B h₁ h₂ := toSubring_injective (le_antisymm h₁.1 h₂.1)

/-- `A` dominates `B` if and only if `B ≤ A` (as subrings) and `m_A ∩ B = m_B`. -/
/-
**LocalSubring.le_def** 是 Mathlib 中的一个引理，位于命名空间 `LocalSubring`。
形式化陈述：le_def {A B : LocalSubring R} : A <= B ↔ exists h : A.toSubring <= B.toSub
ring, IsLocalHom (Subring.inclusion h)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
`A` dominates `B` if and only if `B ≤ A` (as subrings) and `m_A ∩ B = m_B`.
-/
lemma le_def {A B : LocalSubring R} :
    A ≤ B ↔ ∃ h : A.toSubring ≤ B.toSubring, IsLocalHom (Subring.inclusion h) := Iff.rfl
/-
**LocalSubring.toSubring_mono** 是 Mathlib 中的一个引理，位于命名空间 `LocalSubring`。
形式化陈述：toSubring_mono : Monotone (toSubring (R
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toSubring_mono : Monotone (toSubring (R := R)) :=
  fun _ _ e ↦ e.1

section ofPrime

variable (A : Subring K) (P : Ideal A) [P.IsPrime]

set_option backward.isDefEq.respectTransparency false in
/-- The localization of a subring at a prime, as a local subring.
Also see `Localization.subalgebra.ofField` -/
noncomputable
/-
**LocalSubring.ofPrime** 是 Mathlib 中的一个定义，位于命名空间 `LocalSubring`。
形式化陈述：ofPrime (A : Subring K) (P : Ideal A) [P.IsPrime] : LocalSubring K
参数：A : Subring K；P : Ideal A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def ofPrime (A : Subring K) (P : Ideal A) [P.IsPrime] : LocalSubring K :=
  range (IsLocalization.lift (M := P.primeCompl) (S := Localization.AtPrime P)
    (g := A.subtype) (by simp [Ideal.primeCompl, not_imp_not]))
/-
**LocalSubring.le_ofPrime** 是 Mathlib 中的一个引理，位于命名空间 `LocalSubring`。
形式化陈述：le_ofPrime : A <= (ofPrime A P).toSubring
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalization.lift_eq`：lift_eq (x : R) : lift hg ((algebraMap R S) x) =
 g x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma le_ofPrime : A ≤ (ofPrime A P).toSubring := by
  intro x hx
  exact ⟨algebraMap A _ ⟨x, hx⟩, by simp⟩

noncomputable
/-
**LocalSubring.** 是 Mathlib 中的一个实例，位于命名空间 `LocalSubring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Algebra A (ofPrime A P).toSubring := (Subring.inclusion (le_ofPrime A P)).toAlgebra
/-
**LocalSubring.** 是 Mathlib 中的一个实例，位于命名空间 `LocalSubring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsScalarTower A (ofPrime A P).toSubring K := .of_algebraMap_eq (fun _ ↦ rfl)

set_option backward.isDefEq.respectTransparency false in
-- see https://github.com/leanprover-community/mathlib4/issues/29041
set_option linter.unusedSimpArgs false in
/-- The localization of a subring at a prime is indeed isomorphic to its abstract localization. -/
noncomputable
/-
**LocalSubring.ofPrimeEquiv** 是 Mathlib 中的一个定义，位于命名空间 `LocalSubring`。
形式化陈述：ofPrimeEquiv : Localization.AtPrime P ≃ₐ[A] (ofPrime A P).toSubring
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def ofPrimeEquiv : Localization.AtPrime P ≃ₐ[A] (ofPrime A P).toSubring := by
  refine AlgEquiv.ofInjective (IsLocalization.liftAlgHom (M := P.primeCompl)
    (S := Localization.AtPrime P) (f := Algebra.ofId A K) _) ?_
  intro x y e
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq P.primeCompl x
  obtain ⟨y, t, rfl⟩ := IsLocalization.exists_mk'_eq P.primeCompl y
  have H : ∀ x : P.primeCompl, x.1 ≠ 0 := by rintro ⟨x, hx⟩ rfl; aesop
  have : x.1 = y.1 * t.1.1⁻¹ * s.1.1 := by
    simpa [IsLocalization.lift_mk', Algebra.ofId_apply, H,
      Algebra.algebraMap_ofSubsemiring_apply, IsUnit.coe_liftRight] using congr($e * s.1.1)
  rw [IsLocalization.mk'_eq_iff_eq]
  congr 1
  ext
  simp [field, H t, this, mul_comm]
/-
**LocalSubring.** 是 Mathlib 中的一个实例，位于命名空间 `LocalSubring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsLocalization.AtPrime (ofPrime A P).toSubring P :=
  IsLocalization.isLocalization_of_algEquiv _ (ofPrimeEquiv A P)

end ofPrime

end LocalSubring

