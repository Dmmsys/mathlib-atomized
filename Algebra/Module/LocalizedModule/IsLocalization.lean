/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Jujian Zhang
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Module.LocalizedModule.Basic

/-!
# Equivalence between `IsLocalizedModule` and `IsLocalization`
-/

public section

section IsLocalizedModule

variable {R : Type*} [CommSemiring R] (S : Submonoid R)
variable {A Aₛ : Type*} [CommSemiring A] [Algebra R A]
variable [CommSemiring Aₛ] [Algebra A Aₛ] [Algebra R Aₛ] [IsScalarTower R A Aₛ]

variable {S} in
/-
**isLocalizedModule_iff_isLocalization** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLocalizedModule_iff_isLocalization : IsLocalizedModule S (IsScalarTower.
toAlgHom R A Aₛ).toLinearMap ↔ IsLocalization (Algebra.algebraMapSubmonoid A S) 
Aₛ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isLocalizedModule_iff`：∀ {R : Type u_1} [inst : CommSemiring R] {M : Typ
e u_2} {M' : Type u_3} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M'] 
[inst_3 : _…
· 使用定理 `isLocalization_iff`：isLocalization_iff : IsLocalization M S ↔ (forall y 
: M, IsUnit (algebraMap R S y)) ∧ (forall z : S, exists x : R × M, z * algebraMa
p R S x.…
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
-/
theorem isLocalizedModule_iff_isLocalization :
    IsLocalizedModule S (IsScalarTower.toAlgHom R A Aₛ).toLinearMap ↔
      IsLocalization (Algebra.algebraMapSubmonoid A S) Aₛ := by
  rw [isLocalizedModule_iff, isLocalization_iff]
  refine and_congr ?_ (and_congr (forall_congr' fun _ ↦ ?_) (forall₂_congr fun _ _ ↦ ?_))
  · simp_rw [← (Algebra.lmul R Aₛ).commutes, Algebra.lmul_isUnit_iff, Subtype.forall,
      Algebra.algebraMapSubmonoid, ← SetLike.mem_coe, Submonoid.coe_map,
      Set.forall_mem_image, ← IsScalarTower.algebraMap_apply]
  · simp_rw [Prod.exists, Subtype.exists, Algebra.algebraMapSubmonoid]
    simp [← IsScalarTower.algebraMap_apply, Submonoid.mk_smul, Algebra.smul_def, mul_comm]
  · congr!; simp_rw [Subtype.exists, Algebra.algebraMapSubmonoid]; simp [Algebra.smul_def]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsLocalization (Algebra.algebraMapSubmonoid A S) Aₛ] :
    IsLocalizedModule S (IsScalarTower.toAlgHom R A Aₛ).toLinearMap :=
  isLocalizedModule_iff_isLocalization.mpr ‹_›

variable (A)

/-- `A` is a localization of a commutative semiring `R` with respect to `S` iff
the associated linear map `R →ₗ[R] A` is a localization of modules with respect to `S`. -/
/-
**isLocalizedModule_iff_isLocalization'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isLocalizedModule_iff_isLocalization' : IsLocalizedModule S (Algebra.linea
rMap R A) ↔ IsLocalization S A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Submonoid.map_id`：map_id (S : Submonoid M) : S.map (MonoidHom.id M) = S
· 使用定理 `isLocalizedModule_iff_isLocalization`：isLocalizedModule_iff_isLocalizati
on : IsLocalizedModule S (IsScalarTower.toAlgHom R A Aₛ).toLinearMap ↔ IsLocaliz
ation (Algebra.algebraMapS…

--- 原说明 ---
`A` is a localization of a commutative semiring `R` with respect to `S` iff
the associated linear map `R →ₗ[R] A` is a localization of modules with respect 
to `S`.
-/
lemma isLocalizedModule_iff_isLocalization' :
    IsLocalizedModule S (Algebra.linearMap R A) ↔ IsLocalization S A := by
  convert! isLocalizedModule_iff_isLocalization (S := S) (A := R) (Aₛ := A)
  exact (Submonoid.map_id S).symm
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsLocalization S A] : IsLocalizedModule S (Algebra.linearMap R A) :=
  (isLocalizedModule_iff_isLocalization' S _).mpr inferInstance

variable {S A} in
/-- `IsLocalization.mk'` agrees with `IsLocalizedModule.mk'`. -/
/-
**IsLocalization.mk'_algebraMap_eq_mk'** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization
`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {S : Submonoid R} {A : Type u_2} 
{Aₛ : Type u_3} [inst_1 : CommSemiring A]   [inst_2 : Algebra R A] [inst_3 : Com
mSemiring Aₛ] [inst_4 : Algebra A Aₛ] [inst_5 : Algebra R Aₛ]   [inst_6 : IsScal
arTower R A Aₛ] [inst_7 : IsLocalization (Algebra.algebraMapSubmonoid A S) Aₛ] {
x : A} {s : ↥S},   IsLocalization.mk' Aₛ x ⟨(algebraMap R A) ↑s, ⋯⟩ =     IsLoca
lizedModule.mk' (IsScalarTower.toAlgHom R A Aₛ).toLinearMap x s
参数：Algebra.algebraMapSubmonoid A S；algebraMap R A；IsScalarTower.toAlgHom R A Aₛ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `Algebra.mem_algebraMapSubmonoid_of_mem`：mem_algebraMapSubmonoid_of_mem {
M : Submonoid R} (x : M) : algebraMap R S x in algebraMapSubmonoid S M
· 使用定理 `instIsLocalizedModuleToLinearMapToAlgHomOfIsLocalizationAlgebraMapSubmon
oid`：∀ {R : Type u_1} [inst : CommSemiring R] (S : Submonoid R) {A : Type u_2} {
Aₛ : Type u_3} [inst_1 : CommSemiring A]   [inst_2 : Algebra R A]…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalizedModule.smul_inj`：smul_inj (s : S) (m₁ m₂ : M') : s • m₁ = s •
 m₂ ↔ m₁ = m₂
· 使用定理 `IsLocalizedModule.mk'_cancel'`：∀ {R : Type u_1} [inst : CommSemiring R] 
{S : Submonoid R} {M : Type u_2} {M' : Type u_3} [inst_1 : AddCommMonoid M]   [i
nst_2 : AddCommMono…
· 使用定理 `Submonoid.smul_def`：∀ {M' : Type u_1} {α : Type u_2} [inst : MulOneClass
 M'] [inst_1 : SMul M' α] {S : Submonoid M'} (g : ↥S) (a : α),   g • a = ↑g • a
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
· 使用定理 `IsLocalization.smul_mk'_self`：∀ {R : Type u_1} [inst : CommSemiring R] {
M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…

--- 原说明 ---
`IsLocalization.mk'` agrees with `IsLocalizedModule.mk'`.
-/
lemma IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization (Algebra.algebraMapSubmonoid A S) Aₛ]
    {x : A} {s : S} : IsLocalization.mk' Aₛ x ⟨_, Algebra.mem_algebraMapSubmonoid_of_mem s⟩ =
      IsLocalizedModule.mk' (IsScalarTower.toAlgHom R A Aₛ).toLinearMap x s := by
  rw [← IsLocalizedModule.smul_inj (IsScalarTower.toAlgHom R A Aₛ).toLinearMap s,
    IsLocalizedModule.mk'_cancel', Submonoid.smul_def, ← algebraMap_smul A]
  exact IsLocalization.smul_mk'_self (m := ⟨_, _⟩)

/-- `IsLocalization.mk'` agrees with `IsLocalizedModule.mk'`. -/
/-
**IsLocalization.mk'_eq_mk'** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (S : Submonoid R) (A : Type u_2) 
[inst_1 : CommSemiring A]   [inst_2 : Algebra R A] [inst_3 : IsLocalization S A]
 (x : R) (s : ↥S),   IsLocalization.mk' A x s = IsLocalizedModule.mk' (Algebra.l
inearMap R A) x s
参数：S : Submonoid R；A : Type u_2；x : R；s : ↥S；Algebra.linearMap R A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `instIsLocalizedModuleLinearMapOfIsLocalization`：∀ {R : Type u_1} [inst :
 CommSemiring R] (S : Submonoid R) (A : Type u_2) [inst_1 : CommSemiring A]   [i
nst_2 : Algebra R A] [IsLocalization…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalizedModule.smul_inj`：smul_inj (s : S) (m₁ m₂ : M') : s • m₁ = s •
 m₂ ↔ m₁ = m₂
· 使用定理 `IsLocalizedModule.mk'_cancel'`：∀ {R : Type u_1} [inst : CommSemiring R] 
{S : Submonoid R} {M : Type u_2} {M' : Type u_3} [inst_1 : AddCommMonoid M]   [i
nst_2 : AddCommMono…
· 使用定理 `IsLocalization.smul_mk'_self`：∀ {R : Type u_1} [inst : CommSemiring R] {
M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…

--- 原说明 ---
`IsLocalization.mk'` agrees with `IsLocalizedModule.mk'`.
-/
lemma IsLocalization.mk'_eq_mk' [IsLocalization S A] (x : R) (s : S) :
    IsLocalization.mk' A x s = IsLocalizedModule.mk' (Algebra.linearMap R A) x s := by
  rw [← IsLocalizedModule.smul_inj (Algebra.linearMap R A) s, IsLocalizedModule.mk'_cancel']
  exact IsLocalization.smul_mk'_self

end IsLocalizedModule

