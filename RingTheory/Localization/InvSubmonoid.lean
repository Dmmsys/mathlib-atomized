/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
module

public import Mathlib.GroupTheory.Submonoid.Inverses
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.Defs

/-!
# Submonoid of inverses

## Main definitions

* `IsLocalization.invSubmonoid M S` is the submonoid of `S = M⁻¹R` consisting of inverses of
  each element `x ∈ M`

## Implementation notes

See `Mathlib/RingTheory/Localization/Basic.lean` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/

@[expose] public section


variable {R : Type*} [CommRing R] (M : Submonoid R) (S : Type*) [CommRing S]
variable [Algebra R S]

open Function

namespace IsLocalization

section InvSubmonoid

/-- The submonoid of `S = M⁻¹R` consisting of `{ 1 / x | x ∈ M }`. -/
/-
**IsLocalization.invSubmonoid** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalization`。
形式化陈述：invSubmonoid : Submonoid S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The submonoid of `S = M⁻¹R` consisting of `{ 1 / x | x ∈ M }`.
-/
def invSubmonoid : Submonoid S :=
  (M.map (algebraMap R S)).leftInv

variable [IsLocalization M S]
/-
**IsLocalization.submonoid_map_le_is_unit** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalizat
ion`。
形式化陈述：submonoid_map_le_is_unit : M.map (algebraMap R S) <= IsUnit.submonoid S
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IsLocalization.map_units`：map_units : forall y : M, IsUnit (algebraMap R
 S y)
-/
theorem submonoid_map_le_is_unit : M.map (algebraMap R S) ≤ IsUnit.submonoid S := by
  rintro _ ⟨a, ha, rfl⟩
  exact IsLocalization.map_units S ⟨_, ha⟩

/-- There is an equivalence of monoids between the image of `M` and `invSubmonoid`. -/
/-
**IsLocalization.equivInvSubmonoid** 是 Mathlib 中的一个缩写定义，位于命名空间 `IsLocalization`。
形式化陈述：equivInvSubmonoid : M.map (algebraMap R S) ≃* invSubmonoid M S
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.submonoid_map_le_is_unit`：submonoid_map_le_is_unit : M.ma
p (algebraMap R S) <= IsUnit.submonoid S

--- 原说明 ---
There is an equivalence of monoids between the image of `M` and `invSubmonoid`.
-/
noncomputable abbrev equivInvSubmonoid : M.map (algebraMap R S) ≃* invSubmonoid M S :=
  ((M.map (algebraMap R S)).leftInvEquiv (submonoid_map_le_is_unit M S)).symm

/-- There is a canonical map from `M` to `invSubmonoid` sending `x` to `1 / x`. -/
/-
**IsLocalization.toInvSubmonoid** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalization`。
形式化陈述：toInvSubmonoid : M ->* invSubmonoid M S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
There is a canonical map from `M` to `invSubmonoid` sending `x` to `1 / x`.
-/
noncomputable def toInvSubmonoid : M →* invSubmonoid M S :=
  (equivInvSubmonoid M S).toMonoidHom.comp ((algebraMap R S : R →* S).submonoidMap M)
/-
**IsLocalization.toInvSubmonoid_surjective** 是 Mathlib 中的一个定理，位于命名空间 `IsLocaliza
tion`。
形式化陈述：toInvSubmonoid_surjective : Function.Surjective (toInvSubmonoid M S)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `MonoidHom.submonoidMap_surjective`：submonoidMap_surjective (f : M ->* N)
 (M' : Submonoid M) : Function.Surjective (f.submonoidMap M')
-/
theorem toInvSubmonoid_surjective : Function.Surjective (toInvSubmonoid M S) :=
  Function.Surjective.comp (β := M.map (algebraMap R S))
    (Equiv.surjective (equivInvSubmonoid _ _).toEquiv) (MonoidHom.submonoidMap_surjective _ _)

@[simp]
/-
**IsLocalization.toInvSubmonoid_mul** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：toInvSubmonoid_mul (m : M) : (toInvSubmonoid M S m : S) * algebraMap R S m
 = 1
参数：m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.leftInvEquiv_symm_mul`：leftInvEquiv_symm_mul (x : S) : ((S.lef
tInvEquiv hS).symm x : M) * x = 1
· 使用定理 `IsLocalization.submonoid_map_le_is_unit`：submonoid_map_le_is_unit : M.ma
p (algebraMap R S) <= IsUnit.submonoid S
-/
theorem toInvSubmonoid_mul (m : M) : (toInvSubmonoid M S m : S) * algebraMap R S m = 1 :=
  Submonoid.leftInvEquiv_symm_mul _ (submonoid_map_le_is_unit _ _) _

@[simp]
/-
**IsLocalization.mul_toInvSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：mul_toInvSubmonoid (m : M) : algebraMap R S m * (toInvSubmonoid M S m : S)
 = 1
参数：m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.mul_leftInvEquiv_symm`：mul_leftInvEquiv_symm (x : S) : (x : M)
 * (S.leftInvEquiv hS).symm x = 1
· 使用定理 `IsLocalization.submonoid_map_le_is_unit`：submonoid_map_le_is_unit : M.ma
p (algebraMap R S) <= IsUnit.submonoid S
-/
theorem mul_toInvSubmonoid (m : M) : algebraMap R S m * (toInvSubmonoid M S m : S) = 1 :=
  Submonoid.mul_leftInvEquiv_symm _ (submonoid_map_le_is_unit _ _) ⟨_, _⟩

@[simp]
/-
**IsLocalization.smul_toInvSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：smul_toInvSubmonoid (m : M) : m • (toInvSubmonoid M S m : S) = 1
参数：m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `IsLocalization.mul_toInvSubmonoid`：mul_toInvSubmonoid (m : M) : algebraM
ap R S m * (toInvSubmonoid M S m : S) = 1
-/
theorem smul_toInvSubmonoid (m : M) : m • (toInvSubmonoid M S m : S) = 1 := by
  convert! mul_toInvSubmonoid M S m
  ext
  rw [← Algebra.smul_def]
  rfl

variable {S}

-- `surj'` was taken, so use `surj''` instead
-- TODO: this can be fixed after the deprecations of 2025-09-04 are removed.
/-
**IsLocalization.surj''** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：surj'' (z : S) : exists (r : R) (m : M), z = r • (toInvSubmonoid M S m : S
)
参数：z : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.surj`：surj : forall z : S, exists x : R × M, z * algebraM
ap R S x.2 = algebraMap R S x.1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsLocalization.mul_toInvSubmonoid`：mul_toInvSubmonoid (m : M) : algebraM
ap R S m * (toInvSubmonoid M S m : S) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem surj'' (z : S) : ∃ (r : R) (m : M), z = r • (toInvSubmonoid M S m : S) := by
  rcases IsLocalization.surj M z with ⟨⟨r, m⟩, e : z * _ = algebraMap R S r⟩
  refine ⟨r, m, ?_⟩
  rw [Algebra.smul_def, ← e, mul_assoc]
  simp
/-
**IsLocalization.toInvSubmonoid_eq_mk'** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization
`。
形式化陈述：toInvSubmonoid_eq_mk' (x : M) : (toInvSubmonoid M S x : S) = mk' S 1 x
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsUnit.mul_left_inj`：mul_left_inj (h : IsUnit a) : b * a = c * a ↔ b = c
· 使用定理 `IsLocalization.map_units`：map_units : forall y : M, IsUnit (algebraMap R
 S y)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsLocalization.toInvSubmonoid_mul`：toInvSubmonoid_mul (m : M) : (toInvSu
bmonoid M S m : S) * algebraMap R S m = 1
· 使用定理 `IsLocalization.mk'_spec`：∀ {R : Type u_1} [inst : CommSemiring R] {M : S
ubmonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [i
nst_3 : IsLoc…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toInvSubmonoid_eq_mk' (x : M) : (toInvSubmonoid M S x : S) = mk' S 1 x := by
  rw [← (IsLocalization.map_units S x).mul_left_inj]
  simp
/-
**IsLocalization.mem_invSubmonoid_iff_exists_mk'** 是 Mathlib 中的一个定理，位于命名空间 `IsLo
calization`。
形式化陈述：mem_invSubmonoid_iff_exists_mk' (x : S) : x in invSubmonoid M S ↔ exists m
 : M, mk' S 1 m = x
参数：x : S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsLocalization.toInvSubmonoid_surjective`：toInvSubmonoid_surjective : Fu
nction.Surjective (toInvSubmonoid M S)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem mem_invSubmonoid_iff_exists_mk' (x : S) :
    x ∈ invSubmonoid M S ↔ ∃ m : M, mk' S 1 m = x := by
  simp_rw [← toInvSubmonoid_eq_mk']
  exact ⟨fun h => ⟨_, congr_arg Subtype.val (toInvSubmonoid_surjective M S ⟨x, h⟩).choose_spec⟩,
    fun h => h.choose_spec ▸ (toInvSubmonoid M S h.choose).prop⟩

variable (S)
/-
**IsLocalization.span_invSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：span_invSubmonoid : Submodule.span R (invSubmonoid M S : Set S) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `IsLocalization.surj''`：surj'' (z : S) : exists (r : R) (m : M), z = r • 
(toInvSubmonoid M S m : S)
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem span_invSubmonoid : Submodule.span R (invSubmonoid M S : Set S) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  rcases IsLocalization.surj'' M x with ⟨r, m, rfl⟩
  exact Submodule.smul_mem _ _ (Submodule.subset_span (toInvSubmonoid M S m).prop)
/-
**IsLocalization.finiteType_of_monoid_fg** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalizati
on`。
形式化陈述：finiteType_of_monoid_fg [Monoid.FG M] : Algebra.FiniteType R S
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monoid.fg_of_surjective`：Monoid.fg_of_surjective {M' : Type*} [Monoid M'
] [Monoid.FG M] (f : M ->* M') (hf : Function.Surjective f) : Monoid.FG M'
· 使用定理 `IsLocalization.toInvSubmonoid_surjective`：toInvSubmonoid_surjective : Fu
nction.Surjective (toInvSubmonoid M S)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Monoid.fg_iff_submonoid_fg`：Monoid.fg_iff_submonoid_fg (N : Submonoid M)
 : Monoid.FG N ↔ N.FG
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Algebra.adjoin_eq_span`：adjoin_eq_span : Subalgebra.toSubmodule (adjoin 
R s) = span R (Submonoid.closure s)
· 使用定理 `IsLocalization.span_invSubmonoid`：span_invSubmonoid : Submodule.span R (
invSubmonoid M S : Set S) = ⊤
-/
theorem finiteType_of_monoid_fg [Monoid.FG M] : Algebra.FiniteType R S := by
  have := Monoid.fg_of_surjective _ (toInvSubmonoid_surjective M S)
  rw [Monoid.fg_iff_submonoid_fg] at this
  rcases this with ⟨s, hs⟩
  refine ⟨⟨s, ?_⟩⟩
  rw [eq_top_iff]
  rintro x -
  change x ∈ (Subalgebra.toSubmodule (Algebra.adjoin R _ : Subalgebra R S) : Set S)
  rw [Algebra.adjoin_eq_span, hs, span_invSubmonoid]
  trivial
/-
**IsLocalization.** 是 Mathlib 中的一个实例，位于命名空间 `IsLocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    (M : Submonoid S) [Monoid.FG M] : Algebra.FiniteType R (Localization M) :=
  .trans ‹_› (IsLocalization.finiteType_of_monoid_fg M _)

end InvSubmonoid

end IsLocalization

