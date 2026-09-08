/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.Algebra.Algebra.Operations

/-!
# Localization of Submodules

Results about localizations of submodules and quotient modules are provided in this file.

## Main results
- `Submodule.localized`:
  The localization of an `R`-submodule of `M` at `p` viewed as an `Rₚ`-submodule of `Mₚ`.
  A direct consequence of this is that `Rₚ` is flat over `R`; see `IsLocalization.flat`.
- `Submodule.toLocalized`:
  The localization map of a submodule `M' →ₗ[R] M'.localized p`.
- `Submodule.toLocalizedQuotient`:
  The localization map of a quotient module `M ⧸ M' →ₗ[R] LocalizedModule p M ⧸ M'.localized p`.

## TODO
- Statements regarding the exactness of localization.

-/

@[expose] public section

open nonZeroDivisors

variable {R S M N : Type*}
variable (S) [CommSemiring R] [CommSemiring S] [AddCommMonoid M] [AddCommMonoid N]
variable [Module R M] [Module R N] [Algebra R S] [Module S N] [IsScalarTower R S N]
variable (p : Submonoid R) [IsLocalization p S] (f : M →ₗ[R] N) [IsLocalizedModule p f]
variable (M' M'' : Submodule R M)

namespace Submodule

/-- Let `N` be a localization of an `R`-module `M` at `p`.
This is the localization of an `R`-submodule of `M` viewed as an `R`-submodule of `N`. -/
/-
**Submodule.localized** 是 Mathlib 中的一个缩写定义，位于命名空间 `Submodule`。
形式化陈述：localized : Submodule (Localization p) (LocalizedModule p M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `N` be a localization of an `R`-module `M` at `p`.
This is the localization of an `R`-submodule of `M` viewed as an `R`-submodule o
f `N`.
-/
def localized₀ : Submodule R N where
  carrier := { x | ∃ m ∈ M', ∃ s : p, IsLocalizedModule.mk' f m s = x }
  add_mem' := fun {x y} ⟨m, hm, s, hx⟩ ⟨n, hn, t, hy⟩ ↦ ⟨t • m + s • n, add_mem (M'.smul_mem t hm)
    (M'.smul_mem s hn), s * t, by rw [← hx, ← hy, IsLocalizedModule.mk'_add_mk']⟩
  zero_mem' := ⟨0, zero_mem _, 1, by simp⟩
  smul_mem' r x := by
    rintro ⟨m, hm, s, hx⟩
    exact ⟨r • m, smul_mem M' _ hm, s, by rw [IsLocalizedModule.mk'_smul, hx]⟩

/-- Let `S` be the localization of `R` at `p` and `N` be a localization of `M` at `p`.
This is the localization of an `R`-submodule of `M` viewed as an `S`-submodule of `N`. -/
/-
**Submodule.localized'** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：localized' : Submodule S N where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `S` be the localization of `R` at `p` and `N` be a localization of `M` at `p
`.
This is the localization of an `R`-submodule of `M` viewed as an `S`-submodule o
f `N`.
-/
def localized' : Submodule S N where
  __ := localized₀ p f M'
  smul_mem' := fun r x ⟨m, hm, s, hx⟩ ↦ by
    have ⟨y, t, hyt⟩ := IsLocalization.exists_mk'_eq p r
    exact ⟨y • m, M'.smul_mem y hm, t * s, by simp [← hyt, ← hx, IsLocalizedModule.mk'_smul_mk']⟩
/-
**Submodule.mem_localized** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mem_localized₀ (x : N) :
    x ∈ localized₀ p f M' ↔ ∃ m ∈ M', ∃ s : p, IsLocalizedModule.mk' f m s = x :=
  Iff.rfl
/-
**Submodule.mem_localized'** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：mem_localized' (x : N) : x in localized' S p f M' ↔ exists m in M', exists
 s : p, IsLocalizedModule.mk' f m s = x
参数：x : N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_localized' (x : N) :
    x ∈ localized' S p f M' ↔ ∃ m ∈ M', ∃ s : p, IsLocalizedModule.mk' f m s = x :=
  Iff.rfl

/-- `localized₀` is the same as `localized'` considered as a submodule over the base ring. -/
/-
**Submodule.restrictScalars_localized'** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：restrictScalars_localized' : (localized' S p f M').restrictScalars R = loc
alized₀ p f M'
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`localized₀` is the same as `localized'` considered as a submodule over the base
 ring.
-/
lemma restrictScalars_localized' :
    (localized' S p f M').restrictScalars R = localized₀ p f M' :=
  rfl
/-
**Submodule.localized'_eq_span** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u_1} (S : Type u_2) {M : Type u_3} {N : Type u_4} [inst : Comm
Semiring R] [inst_1 : CommSemiring S]   [inst_2 : AddCommMonoid M] [inst_3 : Add
CommMonoid N] [inst_4 : _root_.Module R M] [inst_5 : _root_.Module R N]   [inst_
6 : Algebra R S] [inst_7 : _root_.Module S N] [inst_8 : IsScalarTower R S N] (p 
: Submonoid R)   [inst_9 : IsLocalization p S] (f : M →ₗ[R] N) [inst_10 : IsLoca
lizedModule p f] (M' : Submodule R M),   Submodule.localized' S p f M' = Submodu
le.span S (⇑f '' ↑M')
参数：S : Type u_2；p : Submonoid R；f : M →ₗ[R] N；M' : Submodule R M；⇑f '' ↑M'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalizedModule.mk'_smul_mk'`：∀ {R : Type u_1} [inst : CommSemiring R]
 {S : Submonoid R} {M : Type u_2} {M' : Type u_3} [inst_1 : AddCommMonoid M]   [
inst_2 : AddCommMono…
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsLocalizedModule.mk'_one`：∀ {R : Type u_1} [inst : CommSemiring R] (S :
 Submonoid R) {M : Type u_2} {M' : Type u_3} [inst_1 : AddCommMonoid M]   [inst_
2 : AddCommMono…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem localized'_eq_span : localized' S p f M' = span S (f '' M') := by
  refine le_antisymm ?_ (span_le.mpr <| by rintro _ ⟨m, hm, rfl⟩; exact ⟨m, hm, 1, by simp⟩)
  rintro _ ⟨m, hm, s, rfl⟩
  rw [← one_smul R m, ← mul_one s, ← IsLocalizedModule.mk'_smul_mk' S]
  exact smul_mem _ _ (subset_span ⟨m, hm, by simp⟩)
/-
**Submodule.map_le_localized** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_le_localized₀ : M'.map f ≤ localized₀ p f M' := by
  rintro - ⟨x, hx, rfl⟩
  rw [mem_localized₀]
  exact ⟨x, hx, 1, IsLocalizedModule.mk'_one p f x⟩

/-- The Galois insertion between `Submodule R M` and `Submodule S N`,
where `S` is the localization of `R` at `p` and `N` is the localization of `M` at `p`. -/
/-
**Submodule.localized'gi** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：{R : Type u_1} →   (S : Type u_2) →     {M : Type u_3} →       {N : Type u
_4} →         [inst : CommSemiring R] →           [inst_1 : CommSemiring S] →   
          [inst_2 : AddCommMonoid M] →               [inst_3 : AddCommMonoid N] 
→                 [inst_4 : _root_.Module R M] →                   [inst_5 : _ro
ot_.Module R N] →                     [inst_6 : Algebra R S] →                  
     [inst_7 : _root_.Module S N] →                         [inst_8 : IsScalarTo
wer R S N] →                           (p : Submonoid R) →                      
       [inst_9 : IsLocalization p S] →                               (f : M →ₗ[R
] N) →                                 [inst_10 : IsLocalizedModule p f] →      
                             GaloisInsertion (Submodule.localized' S p f) fun x 
=>                                     Submodule.comap f (Submodule.restrictScal
ars R x)
参数：S : Type u_2；p : Submonoid R；f : M →ₗ[R] N；Submodule.localized' S p f；Submodu
le.restrictScalars R x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Galois insertion between `Submodule R M` and `Submodule S N`,
where `S` is the localization of `R` at `p` and `N` is the localization of `M` a
t `p`.
-/
def localized'gi : GaloisInsertion (localized' S p f) (comap f <| ·.restrictScalars R) where
  gc M' N' := ⟨fun h m hm ↦ h ⟨m, hm, 1, by simp⟩, fun h ↦ by
    rw [localized'_eq_span, span_le]; apply map_le_iff_le_comap.mpr h⟩
  le_l_u N' n hn := by
    obtain ⟨⟨m, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective p f n
    refine ⟨m, ?_, s, rfl⟩
    rw [mem_comap, restrictScalars_mem, ← IsLocalizedModule.mk'_cancel' _ _ s,
      Submonoid.smul_def, ← algebraMap_smul S]
    exact smul_mem _ _ hn
  choice x _ := localized' S p f x
  choice_eq _ _ := rfl

/-- The localization of an `R`-submodule of `M` at `p` viewed as an `Rₚ`-submodule of `Mₚ`. -/
/-
**Submodule.localized** 是 Mathlib 中的一个缩写定义，位于命名空间 `Submodule`。
形式化陈述：localized : Submodule (Localization p) (LocalizedModule p M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The localization of an `R`-submodule of `M` at `p` viewed as an `Rₚ`-submodule o
f `Mₚ`.
-/
noncomputable abbrev localized : Submodule (Localization p) (LocalizedModule p M) :=
  M'.localized' (Localization p) p (LocalizedModule.mkLinearMap p M)

@[simp]
/-
**Submodule.localized** 是 Mathlib 中的一个缩写定义，位于命名空间 `Submodule`。
形式化陈述：localized : Submodule (Localization p) (LocalizedModule p M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma localized₀_bot : (⊥ : Submodule R M).localized₀ p f = ⊥ := by
  rw [← le_bot_iff]
  rintro _ ⟨_, rfl, s, rfl⟩
  simp only [IsLocalizedModule.mk'_zero, mem_bot]

@[simp]
/-
**Submodule.localized'_bot** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u_1} (S : Type u_2) {M : Type u_3} {N : Type u_4} [inst : Comm
Semiring R] [inst_1 : CommSemiring S]   [inst_2 : AddCommMonoid M] [inst_3 : Add
CommMonoid N] [inst_4 : _root_.Module R M] [inst_5 : _root_.Module R N]   [inst_
6 : Algebra R S] [inst_7 : _root_.Module S N] [inst_8 : IsScalarTower R S N] (p 
: Submonoid R)   [inst_9 : IsLocalization p S] (f : M →ₗ[R] N) [inst_10 : IsLoca
lizedModule p f], Submodule.localized' S p f ⊥ = ⊥
参数：S : Type u_2；p : Submonoid R；f : M →ₗ[R] N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext'`：ext' (h : (p : Set B) = q) : p = q
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.ext'_iff`：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p q
 : A}, p = q ↔ ↑p = ↑q
· 使用引理 `Submodule.localized₀_bot`：localized₀_bot : (⊥ : Submodule R M).localized
₀ p f = ⊥
-/
lemma localized'_bot : (⊥ : Submodule R M).localized' S p f = ⊥ :=
  SetLike.ext' (by apply SetLike.ext'_iff.mp <| Submodule.localized₀_bot p f)

@[simp]
/-
**Submodule.localized** 是 Mathlib 中的一个缩写定义，位于命名空间 `Submodule`。
形式化陈述：localized : Submodule (Localization p) (LocalizedModule p M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma localized₀_top : (⊤ : Submodule R M).localized₀ p f = ⊤ := by
  rw [← top_le_iff]
  rintro x _
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective p f x
  exact ⟨x, trivial, s, rfl⟩

@[simp]
/-
**Submodule.localized'_top** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u_1} (S : Type u_2) {M : Type u_3} {N : Type u_4} [inst : Comm
Semiring R] [inst_1 : CommSemiring S]   [inst_2 : AddCommMonoid M] [inst_3 : Add
CommMonoid N] [inst_4 : _root_.Module R M] [inst_5 : _root_.Module R N]   [inst_
6 : Algebra R S] [inst_7 : _root_.Module S N] [inst_8 : IsScalarTower R S N] (p 
: Submonoid R)   [inst_9 : IsLocalization p S] (f : M →ₗ[R] N) [inst_10 : IsLoca
lizedModule p f], Submodule.localized' S p f ⊤ = ⊤
参数：S : Type u_2；p : Submonoid R；f : M →ₗ[R] N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext'`：ext' (h : (p : Set B) = q) : p = q
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.ext'_iff`：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p q
 : A}, p = q ↔ ↑p = ↑q
· 使用引理 `Submodule.localized₀_top`：localized₀_top : (⊤ : Submodule R M).localized
₀ p f = ⊤
-/
lemma localized'_top : (⊤ : Submodule R M).localized' S p f = ⊤ :=
  SetLike.ext' (by apply SetLike.ext'_iff.mp <| Submodule.localized₀_top p f)
/-
**Submodule.localized** 是 Mathlib 中的一个缩写定义，位于命名空间 `Submodule`。
形式化陈述：localized : Submodule (Localization p) (LocalizedModule p M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem localized₀_inf :
    (M' ⊓ M'').localized₀ p f = M'.localized₀ p f ⊓ M''.localized₀ p f := by
  simp only [Submodule.ext_iff, Submodule.mem_inf, mem_localized₀]
  refine fun x ↦ ⟨by grind, ?_⟩
  rintro ⟨⟨i, hi, s, hs⟩, j, hj, t, ht⟩
  have h := ht.trans hs.symm
  rw [IsLocalizedModule.mk'_eq_mk'_iff] at h
  obtain ⟨k, hk⟩ := h
  refine ⟨(k * t) • i, ⟨M'.smul_of_tower_mem (k * t) hi, ?_⟩, k * s * t, ?_⟩
  · rw [mul_smul, hk, smul_smul]
    exact M''.smul_of_tower_mem (k * s) hj
  · rwa [mul_smul, hk, smul_smul, IsLocalizedModule.mk'_cancel_left]
/-
**Submodule.localized'_inf** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u_1} (S : Type u_2) {M : Type u_3} {N : Type u_4} [inst : Comm
Semiring R] [inst_1 : CommSemiring S]   [inst_2 : AddCommMonoid M] [inst_3 : Add
CommMonoid N] [inst_4 : _root_.Module R M] [inst_5 : _root_.Module R N]   [inst_
6 : Algebra R S] [inst_7 : _root_.Module S N] [inst_8 : IsScalarTower R S N] (p 
: Submonoid R)   [inst_9 : IsLocalization p S] (f : M →ₗ[R] N) [inst_10 : IsLoca
lizedModule p f] (M' M'' : Submodule R M),   Submodule.localized' S p f (M' ⊓ M'
') = Submodule.localized' S p f M' ⊓ Submodule.localized' S p f M''
参数：S : Type u_2；p : Submonoid R；f : M →ₗ[R] N；M' M'' : Submodule R M；M' ⊓ M''。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext'`：ext' (h : (p : Set B) = q) : p = q
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.ext'_iff`：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p q
 : A}, p = q ↔ ↑p = ↑q
· 使用定理 `Submodule.localized₀_inf`：localized₀_inf : (M' ⊓ M'').localized₀ p f = M
'.localized₀ p f ⊓ M''.localized₀ p f
-/
theorem localized'_inf :
    (M' ⊓ M'').localized' S p f = M'.localized' S p f ⊓ M''.localized' S p f :=
  SetLike.ext' (by apply SetLike.ext'_iff.mp <| Submodule.localized₀_inf p f M' M'')
/-
**Submodule.localized'_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u_1} (S : Type u_2) {M : Type u_3} {N : Type u_4} [inst : Comm
Semiring R] [inst_1 : CommSemiring S]   [inst_2 : AddCommMonoid M] [inst_3 : Add
CommMonoid N] [inst_4 : _root_.Module R M] [inst_5 : _root_.Module R N]   [inst_
6 : Algebra R S] [inst_7 : _root_.Module S N] [inst_8 : IsScalarTower R S N] (p 
: Submonoid R)   [inst_9 : IsLocalization p S] (f : M →ₗ[R] N) [inst_10 : IsLoca
lizedModule p f] {ι : Type u_5}   (g : ι → Submodule R M), Submodule.localized' 
S p f (⨆ i, g i) = ⨆ i, Submodule.localized' S p f (g i)
参数：S : Type u_2；p : Submonoid R；f : M →ₗ[R] N；g : ι → Submodule R M；⨆ i, g i；g i
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_iSup`：l_iSup {f : ι -> α} : l (iSup f) = ⨆ i, l (f i)
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
-/
theorem localized'_iSup {ι : Type*} (g : ι → Submodule R M) :
    (⨆ i, g i).localized' S p f = ⨆ i, (g i).localized' S p f := by
  exact GaloisConnection.l_iSup (localized'gi S p f).gc
/-
**Submodule.localized** 是 Mathlib 中的一个缩写定义，位于命名空间 `Submodule`。
形式化陈述：localized : Submodule (Localization p) (LocalizedModule p M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem localized₀_iSup {ι : Type*} (g : ι → Submodule R M) :
    (⨆ i, g i).localized₀ p f = ⨆ i, (g i).localized₀ p f := by
  let : Module (Localization p) N := IsLocalizedModule.module p f
  have : IsScalarTower R (Localization p) N := IsLocalizedModule.isScalarTower_module p f
  simpa using! congr_arg (restrictScalars R) (localized'_iSup (Localization p) p f g)

/-- `localized₀` as a `FrameHom`. -/
/-
**Submodule.localized** 是 Mathlib 中的一个缩写定义，位于命名空间 `Submodule`。
形式化陈述：localized : Submodule (Localization p) (LocalizedModule p M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`localized₀` as a `FrameHom`.
-/
noncomputable def localized₀FrameHom : FrameHom (Submodule R M) (Submodule R N) where
  toFun := localized₀ p f
  map_inf' := localized₀_inf p f
  map_top' := localized₀_top p f
  map_sSup' s := by rw [sSup_eq_iSup', localized₀_iSup, sSup_image']

@[simp]
/-
**Submodule.IsLocalizedModule.localized** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsLocalizedModule.localized₀FrameHom_apply :
    localized₀FrameHom p f M' = M'.localized₀ p f :=
  rfl

/-- `localized'` as a `FrameHom`. -/
/-
**Submodule.localized'FrameHom** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：{R : Type u_1} →   (S : Type u_2) →     {M : Type u_3} →       {N : Type u
_4} →         [inst : CommSemiring R] →           [inst_1 : CommSemiring S] →   
          [inst_2 : AddCommMonoid M] →               [inst_3 : AddCommMonoid N] 
→                 [inst_4 : _root_.Module R M] →                   [inst_5 : _ro
ot_.Module R N] →                     [inst_6 : Algebra R S] →                  
     [inst_7 : _root_.Module S N] →                         [IsScalarTower R S N
] →                           (p : Submonoid R) →                             [I
sLocalization p S] →                               (f : M →ₗ[R] N) → [IsLocalize
dModule p f] → FrameHom (Submodule R M) (Submodule S N)
参数：S : Type u_2；p : Submonoid R；f : M →ₗ[R] N；Submodule R M；Submodule S N。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.localized'_inf`：∀ {R : Type u_1} (S : Type u_2) {M : Type u_3}
 {N : Type u_4} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [inst_2 : Ad
dCommMonoid M]…
· 使用定理 `Submodule.localized'_top`：∀ {R : Type u_1} (S : Type u_2) {M : Type u_3}
 {N : Type u_4} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [inst_2 : Ad
dCommMonoid M]…

--- 原说明 ---
`localized'` as a `FrameHom`.
-/
noncomputable def localized'FrameHom :
    FrameHom (Submodule R M) (Submodule S N) where
  toFun := localized' S p f
  map_inf' := localized'_inf S p f
  map_top' := localized'_top S p f
  map_sSup' s := by rw [sSup_eq_iSup', localized'_iSup, sSup_image']

@[simp]
/-
**Submodule.IsLocalizedModule.localized'FrameHom_apply** 是 Mathlib 中的一个定理，位于命名空间
 `Submodule.IsLocalizedModule`。
形式化陈述：∀ {R : Type u_1} (S : Type u_2) {M : Type u_3} {N : Type u_4} [inst : Comm
Semiring R] [inst_1 : CommSemiring S]   [inst_2 : AddCommMonoid M] [inst_3 : Add
CommMonoid N] [inst_4 : _root_.Module R M] [inst_5 : _root_.Module R N]   [inst_
6 : Algebra R S] [inst_7 : _root_.Module S N] [inst_8 : IsScalarTower R S N] (p 
: Submonoid R)   [inst_9 : IsLocalization p S] (f : M →ₗ[R] N) [inst_10 : IsLoca
lizedModule p f] (M' : Submodule R M),   (Submodule.localized'FrameHom S p f) M'
 = Submodule.localized' S p f M'
参数：S : Type u_2；p : Submonoid R；f : M →ₗ[R] N；M' : Submodule R M；Submodule.local
ized'FrameHom S p f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsLocalizedModule.localized'FrameHom_apply :
    localized'FrameHom S p f M' = M'.localized' S p f :=
  rfl

@[simp]
/-
**Submodule.localized'_span** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u_1} (S : Type u_2) {M : Type u_3} {N : Type u_4} [inst : Comm
Semiring R] [inst_1 : CommSemiring S]   [inst_2 : AddCommMonoid M] [inst_3 : Add
CommMonoid N] [inst_4 : _root_.Module R M] [inst_5 : _root_.Module R N]   [inst_
6 : Algebra R S] [inst_7 : _root_.Module S N] [inst_8 : IsScalarTower R S N] (p 
: Submonoid R)   [inst_9 : IsLocalization p S] (f : M →ₗ[R] N) [inst_10 : IsLoca
lizedModule p f] (s : Set M),   Submodule.localized' S p f (Submodule.span R s) 
= Submodule.span S (⇑f '' s)
参数：S : Type u_2；p : Submonoid R；f : M →ₗ[R] N；s : Set M；Submodule.span R s；⇑f ''
 s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.localized'_eq_span`：∀ {R : Type u_1} (S : Type u_2) {M : Type 
u_3} {N : Type u_4} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [inst_2 
: AddCommMonoid M]…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.map_coe`：map_coe (f : M ->ₛₗ[σ₁₂] M₂) (p : Submodule R M) : (m
ap f p : Set M₂) = f '' p
· 使用定理 `Submodule.map_span`：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂
) (s : Set M) : (span R s).map f = span R₂ (f '' s)
· 使用定理 `Submodule.span_span_of_tower`：span_span_of_tower : span S (span R s : Se
t M) = span S s
-/
lemma localized'_span (s : Set M) : (span R s).localized' S p f = span S (f '' s) := by
  rw [localized'_eq_span, ← map_coe, map_span, span_span_of_tower]
/-
**Submodule.localized** 是 Mathlib 中的一个缩写定义，位于命名空间 `Submodule`。
形式化陈述：localized : Submodule (Localization p) (LocalizedModule p M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma localized₀_smul (I : Submodule R R) : (I • M').localized₀ p f = I • M'.localized₀ p f := by
  apply le_antisymm
  · rintro _ ⟨a, ha, s, rfl⟩
    refine Submodule.smul_induction_on ha ?_ ?_
    · intro r hr n hn
      rw [IsLocalizedModule.mk'_smul]
      exact Submodule.smul_mem_smul hr ⟨n, hn, s, rfl⟩
    · simp +contextual only [IsLocalizedModule.mk'_add, add_mem, implies_true]
  · refine Submodule.smul_le.mpr ?_
    rintro r hr _ ⟨a, ha, s, rfl⟩
    rw [← IsLocalizedModule.mk'_smul]
    exact ⟨_, Submodule.smul_mem_smul hr ha, s, rfl⟩
/-
**Submodule.restrictScalars_localized'_smul** 是 Mathlib 中的一个定理，位于命名空间 `Submodule
`。
形式化陈述：∀ {R : Type u_1} (S : Type u_2) {N : Type u_4} [inst : CommSemiring R] [in
st_1 : CommSemiring S]   [inst_2 : AddCommMonoid N] [inst_3 : _root_.Module R N]
 [inst_4 : Algebra R S] [inst_5 : _root_.Module S N]   [inst_6 : IsScalarTower R
 S N] (p : Submonoid R) [inst_7 : IsLocalization p S] (I : Submodule R R)   (N' 
: Submodule S N),   Submodule.restrictScalars R (Submodule.localized' S p (Algeb
ra.linearMap R S) I • N') =     I • Submodule.restrictScalars R N'
参数：S : Type u_2；p : Submonoid R；I : Submodule R R；N' : Submodule S N；Submodule.l
ocalized' S p (Algebra.linearMap R S) I • N'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `instIsLocalizedModuleLinearMapOfIsLocalization`：∀ {R : Type u_1} [inst :
 CommSemiring R] (S : Submonoid R) (A : Type u_2) [inst_1 : CommSemiring A]   [i
nst_2 : Algebra R A] [IsLocalization…
· 使用定理 `Submodule.smul_induction_on`：smul_induction_on {p : M -> Prop} {x} (H : 
x in I • N) (smul : forall r in I, forall n in N, p (r • n)) (add : forall x y, 
p x -> p y -> p (…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.restrictScalars_mem`：restrictScalars_mem (V : Submodule R M) (
m : M) : m in V.restrictScalars S ↔ m in V
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalization.mk'_eq_mk'`：∀ {R : Type u_1} [inst : CommSemiring R] (S :
 Submonoid R) (A : Type u_2) [inst_1 : CommSemiring A]   [inst_2 : Algebra R A] 
[inst_3 : IsLoc…
· 使用定理 `IsLocalization.mk'_eq_mul_mk'_one`：∀ {R : Type u_1} [inst : CommSemiring
 R] {M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algeb
ra R S] [inst_3 : IsLoc…
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
· 使用定理 `Submodule.smul_mem_smul`：smul_mem_smul {r} {n} (hr : r in I) (hn : n in 
N) : r • n in I • N
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `Submodule.smul_le`：smul_le : I • N <= P ↔ forall r in I, forall n in N, 
r • n in P
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsLocalizedModule.mk'_one`：∀ {R : Type u_1} [inst : CommSemiring R] (S :
 Submonoid R) {M : Type u_2} {M' : Type u_3} [inst_1 : AddCommMonoid M]   [inst_
2 : AddCommMono…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma restrictScalars_localized'_smul (I : Submodule R R) (N' : Submodule S N) :
    (I.localized' S p (Algebra.linearMap R S) • N').restrictScalars R =
      I • N'.restrictScalars R := by
  refine le_antisymm (fun x hx ↦ ?_) (Submodule.smul_le.mpr fun r hr n hn ↦ ?_)
  · refine smul_induction_on ((Submodule.restrictScalars_mem _ _ _).mp hx) ?_ fun _ _ ↦ add_mem
    rintro _ ⟨r, hr, s, rfl⟩ n hn
    rw [← IsLocalization.mk'_eq_mk', IsLocalization.mk'_eq_mul_mk'_one, mul_smul, algebraMap_smul]
    exact smul_mem_smul hr ((Submodule.restrictScalars_mem _ _ _).mpr <| smul_mem _ _ hn)
  · rw [← algebraMap_smul S, Submodule.restrictScalars_mem]
    exact Submodule.smul_mem_smul ⟨_, hr, 1, by simp⟩ hn
/-
**Submodule.localized'_smul** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u_1} (S : Type u_2) {M : Type u_3} {N : Type u_4} [inst : Comm
Semiring R] [inst_1 : CommSemiring S]   [inst_2 : AddCommMonoid M] [inst_3 : Add
CommMonoid N] [inst_4 : _root_.Module R M] [inst_5 : _root_.Module R N]   [inst_
6 : Algebra R S] [inst_7 : _root_.Module S N] [inst_8 : IsScalarTower R S N] (p 
: Submonoid R)   [inst_9 : IsLocalization p S] (f : M →ₗ[R] N) [inst_10 : IsLoca
lizedModule p f] (M' : Submodule R M)   (I : Submodule R R),   Submodule.localiz
ed' S p f (I • M') =     Submodule.localized' S p (Algebra.linearMap R S) I • Su
bmodule.localized' S p f M'
参数：S : Type u_2；p : Submonoid R；f : M →ₗ[R] N；M' : Submodule R M；I : Submodule R
 R；I • M'；Algebra.linearMap R S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.restrictScalars_injective`：restrictScalars_injective : Functio
n.Injective (restrictScalars S : Submodule R M -> Submodule S M)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `instIsLocalizedModuleLinearMapOfIsLocalization`：∀ {R : Type u_1} [inst :
 CommSemiring R] (S : Submonoid R) (A : Type u_2) [inst_1 : CommSemiring A]   [i
nst_2 : Algebra R A] [IsLocalization…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.restrictScalars_localized'_smul`：∀ {R : Type u_1} (S : Type u_
2) {N : Type u_4} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [inst_2 : 
AddCommMonoid N] [inst_3 : _roo…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Submodule.localized₀_smul`：localized₀_smul (I : Submodule R R) : (I • M'
).localized₀ p f = I • M'.localized₀ p f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma localized'_smul (I : Submodule R R) :
    (I • M').localized' S p f = I.localized' S p (Algebra.linearMap R S) • M'.localized' S p f :=
  Submodule.restrictScalars_injective R _ _ <| by
    simp_rw [restrictScalars_localized'_smul, restrictScalars_localized', localized₀_smul]

/-- The localization map of a submodule. -/
@[simps!]
/-
**Submodule.toLocalized** 是 Mathlib 中的一个缩写定义，位于命名空间 `Submodule`。
形式化陈述：toLocalized : M' ->ₗ[R] M'.localized p
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The localization map of a submodule.
-/
def toLocalized₀ : M' →ₗ[R] M'.localized₀ p f := f.restrict fun x hx ↦ ⟨x, hx, 1, by simp⟩

/-- The localization map of a submodule. -/
@[simps!]
/-
**Submodule.toLocalized'** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：toLocalized' : M' ->ₗ[R] M'.localized' S p f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The localization map of a submodule.
-/
def toLocalized' : M' →ₗ[R] M'.localized' S p f := toLocalized₀ p f M'

/-- The localization map of a submodule. -/
/-
**Submodule.toLocalized** 是 Mathlib 中的一个缩写定义，位于命名空间 `Submodule`。
形式化陈述：toLocalized : M' ->ₗ[R] M'.localized p
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The localization map of a submodule.
-/
noncomputable abbrev toLocalized : M' →ₗ[R] M'.localized p :=
  M'.toLocalized' (Localization p) p (LocalizedModule.mkLinearMap p M)
/-
**Submodule.** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsLocalizedModule p (M'.toLocalized₀ p f) where
  map_units x := by
    simp_rw [Module.End.isUnit_iff]
    constructor
    · exact fun _ _ e ↦ Subtype.ext
        (IsLocalizedModule.smul_injective f x (congr_arg Subtype.val e))
    · rintro ⟨_, m, hm, s, rfl⟩
      refine ⟨⟨IsLocalizedModule.mk' f m (s * x), ⟨_, hm, _, rfl⟩⟩, Subtype.ext ?_⟩
      rw [Module.algebraMap_end_apply, SetLike.val_smul_of_tower,
        ← IsLocalizedModule.mk'_smul, ← Submonoid.smul_def, IsLocalizedModule.mk'_cancel_right]
  surj := by
    rintro ⟨y, x, hx, s, rfl⟩
    exact ⟨⟨⟨x, hx⟩, s⟩, by ext; simp⟩
  exists_of_eq e := by simpa [Subtype.ext_iff] using
      IsLocalizedModule.exists_of_eq (S := p) (f := f) (congr_arg Subtype.val e)
/-
**Submodule.isLocalizedModule** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
形式化陈述：isLocalizedModule : IsLocalizedModule p (M'.toLocalized' S p f)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isLocalizedModule : IsLocalizedModule p (M'.toLocalized' S p f) :=
  inferInstanceAs (IsLocalizedModule p (M'.toLocalized₀ p f))

/-- The canonical isomorphism between the localization of a submodule and its realization
as a submodule in the localized module. -/
/-
**Submodule.localizedEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：localizedEquiv : M'.localized p ≃ₗ[Localization p] LocalizedModule p M'
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.linearMap_compatibleSMul`：linearMap_compatibleSMul [Modul
e S N₁] [Module S N₂] [IsScalarTower R S N₁] [IsScalarTower R S N₂] : LinearMap.
CompatibleSMul N₁ N₂ S R wher…

--- 原说明 ---
The canonical isomorphism between the localization of a submodule and its realiz
ation
as a submodule in the localized module.
-/
noncomputable def localizedEquiv : M'.localized p ≃ₗ[Localization p] LocalizedModule p M' :=
  have := IsLocalization.linearMap_compatibleSMul p
  IsLocalizedModule.linearEquiv p (M'.toLocalized p) (LocalizedModule.mkLinearMap _ _)
    |>.restrictScalars _

open scoped Pointwise
/-
**Submodule.localized** 是 Mathlib 中的一个缩写定义，位于命名空间 `Submodule`。
形式化陈述：localized : Submodule (Localization p) (LocalizedModule p M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma localized₀_le_localized₀_of_smul_le {P Q : Submodule R M} (x : p) (h : x • P ≤ Q) :
    P.localized₀ p f ≤ Q.localized₀ p f := by
  rintro - ⟨a, ha, r, rfl⟩
  refine ⟨x • a, h ⟨a, ha, rfl⟩, x * r, ?_⟩
  simp
/-
**Submodule.localized'_le_localized'_of_smul_le** 是 Mathlib 中的一个定理，位于命名空间 `Submo
dule`。
形式化陈述：∀ {R : Type u_1} (S : Type u_2) {M : Type u_3} {N : Type u_4} [inst : Comm
Semiring R] [inst_1 : CommSemiring S]   [inst_2 : AddCommMonoid M] [inst_3 : Add
CommMonoid N] [inst_4 : _root_.Module R M] [inst_5 : _root_.Module R N]   [inst_
6 : Algebra R S] [inst_7 : _root_.Module S N] [inst_8 : IsScalarTower R S N] (p 
: Submonoid R)   [inst_9 : IsLocalization p S] (f : M →ₗ[R] N) [inst_10 : IsLoca
lizedModule p f] {P Q : Submodule R M} (x : ↥p),   x • P ≤ Q → Submodule.localiz
ed' S p f P ≤ Submodule.localized' S p f Q
参数：S : Type u_2；p : Submonoid R；f : M →ₗ[R] N；x : ↥p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Submodule.localized₀_le_localized₀_of_smul_le`：localized₀_le_localized₀_
of_smul_le {P Q : Submodule R M} (x : p) (h : x • P <= Q) : P.localized₀ p f <= 
Q.localized₀ p f
-/
lemma localized'_le_localized'_of_smul_le {P Q : Submodule R M} (x : p) (h : x • P ≤ Q) :
    P.localized' S p f ≤ Q.localized' S p f :=
  localized₀_le_localized₀_of_smul_le p f x h

end Submodule

section Quotient

variable {R S M N : Type*}
variable (S) [CommRing R] [CommRing S] [AddCommGroup M] [AddCommGroup N]
variable [Module R M] [Module R N] [Algebra R S] [Module S N] [IsScalarTower R S N]
variable (p : Submonoid R) [IsLocalization p S] (f : M →ₗ[R] N) [IsLocalizedModule p f]
variable (M' : Submodule R M)

/-- The localization map of a quotient module. -/
/-
**Submodule.toLocalizedQuotient'** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Submodule.toLocalizedQuotient' : M ⧸ M' ->ₗ[R] N ⧸ M'.localized' S p f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The localization map of a quotient module.
-/
def Submodule.toLocalizedQuotient' : M ⧸ M' →ₗ[R] N ⧸ M'.localized' S p f :=
  Submodule.mapQ M' ((M'.localized' S p f).restrictScalars R) f (fun x hx ↦ ⟨x, hx, 1, by simp⟩)

/-- The localization map of a quotient module. -/
/-
**Submodule.toLocalizedQuotient** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Submodule.toLocalizedQuotient : M ⧸ M' ->ₗ[R] LocalizedModule p M ⧸ M'.loc
alized p
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The localization map of a quotient module.
-/
noncomputable abbrev Submodule.toLocalizedQuotient :
    M ⧸ M' →ₗ[R] LocalizedModule p M ⧸ M'.localized p :=
  M'.toLocalizedQuotient' (Localization p) p (LocalizedModule.mkLinearMap p M)

@[simp]
/-
**Submodule.toLocalizedQuotient'_mk** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u_5} (S : Type u_6) {M : Type u_7} {N : Type u_8} [inst : Comm
Ring R] [inst_1 : CommRing S]   [inst_2 : AddCommGroup M] [inst_3 : AddCommGroup
 N] [inst_4 : _root_.Module R M] [inst_5 : _root_.Module R N]   [inst_6 : Algebr
a R S] [inst_7 : _root_.Module S N] [inst_8 : IsScalarTower R S N] (p : Submonoi
d R)   [inst_9 : IsLocalization p S] (f : M →ₗ[R] N) [inst_10 : IsLocalizedModul
e p f] (M' : Submodule R M) (x : M),   (Submodule.toLocalizedQuotient' S p f M')
 (Submodule.Quotient.mk x) = Submodule.Quotient.mk (f x)
参数：S : Type u_6；p : Submonoid R；f : M →ₗ[R] N；M' : Submodule R M；x : M；Submodule
.toLocalizedQuotient' S p f M'；Submodule.Quotient.mk x；f x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Submodule.toLocalizedQuotient'_mk (x : M) :
    M'.toLocalizedQuotient' S p f (Submodule.Quotient.mk x) = Submodule.Quotient.mk (f x) := rfl

open Submodule Submodule.Quotient IsLocalization in
/-
**IsLocalizedModule.toLocalizedQuotient'** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IsLocalizedModule.toLocalizedQuotient' (M' : Submodule R M) : IsLocalizedM
odule p (M'.toLocalizedQuotient' S p f) where map_units x
参数：M' : Submodule R M。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Module.End.isUnit_iff`：∀ {R : Type u_1} {M : Type u_5} [inst : Semiring 
R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (f : Module.End R M
), IsUnit f…
· 使用定理 `Submodule.Quotient.mk_surjective`：mk_surjective : Function.Surjective (@
mk _ _ _ _ _ p)
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.Quotient.eq`：∀ {R : Type u_1} {M : Type u_2} [inst : Ring R] [
inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   (p : Submodule R M) {x y
 : M}, Subm…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `IsLocalization.mk'_self'`：∀ {R : Type u_1} [inst : CommSemiring R] {M : 
Submonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [
inst_3 : IsLoc…
· 使用定理 `IsLocalization.smul_mk'_one`：∀ {R : Type u_1} [inst : CommSemiring R] {M
 : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R S
] [inst_3 : IsLoc…
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `Module.algebraMap_end_apply`：algebraMap_end_apply (a : R) (m : M) : alge
braMap R (End S M) a m = a • m
· 使用定理 `IsLocalizedModule.mk'_surjective`：∀ {R : Type u_1} [inst : CommSemiring 
R] (S : Submonoid R) {M : Type u_2} {M' : Type u_3} [inst_1 : AddCommMonoid M]  
 [inst_2 : AddCommMono…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsLocalizedModule.mk'_cancel'`：∀ {R : Type u_1} [inst : CommSemiring R] 
{S : Submonoid R} {M : Type u_2} {M' : Type u_3} [inst_1 : AddCommMonoid M]   [i
nst_2 : AddCommMono…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `IsLocalizedModule.exists_of_eq`：∀ {R : Type u_1} {inst : CommSemiring R}
 {M : Type u_2} {M' : Type u_3} {inst_1 : AddCommMonoid M}   {inst_2 : AddCommMo
noid M'} {inst_3 : _…
· 使用定理 `LinearMap.map_smul_of_tower`：map_smul_of_tower [CompatibleSMul M M₂ R S]
 (fₗ : M ->ₗ[S] M₂) (c : R) (x : M) : fₗ (c • x) = c • fₗ x
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
（共 31 条，此处仅展示前 30 条）
-/
instance IsLocalizedModule.toLocalizedQuotient' (M' : Submodule R M) :
    IsLocalizedModule p (M'.toLocalizedQuotient' S p f) where
  map_units x := by
    refine (Module.End.isUnit_iff _).mpr ⟨fun m n e ↦ ?_, fun m ↦ ⟨(IsLocalization.mk' S 1 x) • m,
      by rw [Module.algebraMap_end_apply, ← smul_assoc, smul_mk'_one, mk'_self', one_smul]⟩⟩
    obtain ⟨⟨m, rfl⟩, n, rfl⟩ := PProd.mk (mk_surjective _ m) (mk_surjective _ n)
    simp only [Module.algebraMap_end_apply, ← mk_smul, Submodule.Quotient.eq, ← smul_sub] at e
    replace e := Submodule.smul_mem _ (IsLocalization.mk' S 1 x) e
    rwa [smul_comm, ← smul_assoc, smul_mk'_one, mk'_self', one_smul, ← Submodule.Quotient.eq] at e
  surj y := by
    obtain ⟨y, rfl⟩ := mk_surjective _ y
    obtain ⟨⟨y, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective p f y
    exact ⟨⟨Submodule.Quotient.mk y, s⟩,
      by simp only [Function.uncurry_apply_pair, toLocalizedQuotient'_mk, ← mk_smul, mk'_cancel']⟩
  exists_of_eq {m n} e := by
    obtain ⟨⟨m, rfl⟩, n, rfl⟩ := PProd.mk (mk_surjective _ m) (mk_surjective _ n)
    obtain ⟨x, hx, s, hs⟩ : f (m - n) ∈ _ := by simpa [Submodule.Quotient.eq] using! e
    obtain ⟨c, hc⟩ := exists_of_eq (S := p) (show f (s • (m - n)) = f x by simp [-map_sub, ← hs])
    exact ⟨c * s, by simpa only [← Quotient.mk_smul, Submodule.Quotient.eq,
      ← smul_sub, mul_smul, hc] using! M'.smul_mem c hx⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (M' : Submodule R M) : IsLocalizedModule p (M'.toLocalizedQuotient p) :=
  IsLocalizedModule.toLocalizedQuotient' _ _ _ _

/-- The canonical isomorphism between the localization of a quotient module and its realization
as a quotient of the localized module. -/
/-
**localizedQuotientEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：localizedQuotientEquiv : (LocalizedModule p M ⧸ M'.localized p) ≃ₗ[Localiz
ation p] LocalizedModule p (M ⧸ M')
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instIsLocalizedModuleQuotientSubmoduleLocalizedModuleLocalizationLocaliz
edToLocalizedQuotient`：∀ {R : Type u_5} {M : Type u_7} [inst : CommRing R] [inst
_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   (p : Submonoid R) (M' : Subm
odu…

--- 原说明 ---
The canonical isomorphism between the localization of a quotient module and its 
realization
as a quotient of the localized module.
-/
noncomputable def localizedQuotientEquiv :
    (LocalizedModule p M ⧸ M'.localized p) ≃ₗ[Localization p] LocalizedModule p (M ⧸ M') :=
  have := IsLocalization.linearMap_compatibleSMul p
  IsLocalizedModule.linearEquiv p (M'.toLocalizedQuotient p) (LocalizedModule.mkLinearMap _ _)
    |>.restrictScalars _

end Quotient

namespace LinearMap

variable {P : Type*} [AddCommMonoid P] [Module R P]
variable {Q : Type*} [AddCommMonoid Q] [Module R Q] [Module S Q] [IsScalarTower R S Q]
variable (f' : P →ₗ[R] Q) [IsLocalizedModule p f']

open Submodule IsLocalizedModule

/-
**LinearMap.ker_localizedMap_eq_localized** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ker_localizedMap_eq_localized₀_ker (g : M →ₗ[R] P) :
    ker (map p f f' g) = (ker g).localized₀ p f := by
  ext x
  simp only [Submodule.mem_localized₀, mem_ker]
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalizedModule.mk'_surjective p f x
    simp only [Function.uncurry_apply_pair, map_mk', mk'_eq_zero, eq_zero_iff p f'] at h
    obtain ⟨c, hc⟩ := h
    refine ⟨c • a, by simpa, c * b, by simp⟩
  · rintro ⟨m, hm, a, ha, rfl⟩
    simp [IsLocalizedModule.map_mk', hm]
/-
**LinearMap.localized'_ker_eq_ker_localizedMap** 是 Mathlib 中的一个定理，位于命名空间 `Linear
Map`。
形式化陈述：∀ {R : Type u_1} (S : Type u_2) {M : Type u_3} {N : Type u_4} [inst : Comm
Semiring R] [inst_1 : CommSemiring S]   [inst_2 : AddCommMonoid M] [inst_3 : Add
CommMonoid N] [inst_4 : _root_.Module R M] [inst_5 : _root_.Module R N]   [inst_
6 : Algebra R S] [inst_7 : _root_.Module S N] [inst_8 : IsScalarTower R S N] (p 
: Submonoid R)   [inst_9 : IsLocalization p S] (f : M →ₗ[R] N) [inst_10 : IsLoca
lizedModule p f] {P : Type u_5}   [inst_11 : AddCommMonoid P] [inst_12 : _root_.
Module R P] {Q : Type u_6} [inst_13 : AddCommMonoid Q]   [inst_14 : _root_.Modul
e R Q] [inst_15 : _root_.Module S Q] [inst_16 : IsScalarTower R S Q] (f' : P →ₗ[
R] Q)   [inst_17 : IsLocalizedModule p f'] (g : M →ₗ[R] P),   Submodule.localize
d' S p f g.ker =     (LinearMap.extendScalarsOfIsLocalization p S ((IsLocalizedM
odule.map p f f') g)).ker
参数：S : Type u_2；p : Submonoid R；f : M →ₗ[R] N；f' : P →ₗ[R] Q；g : M →ₗ[R] P；Linea
rMap.extendScalarsOfIsLocalization p S ((IsLocalizedModule.map p f f') g)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.ext_iff`：ext_iff : p = q ↔ forall x, x in p ↔ x in q
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LinearMap.ker_localizedMap_eq_localized₀_ker`：ker_localizedMap_eq_locali
zed₀_ker (g : M ->ₗ[R] P) : ker (map p f f' g) = (ker g).localized₀ p f
-/
lemma localized'_ker_eq_ker_localizedMap (g : M →ₗ[R] P) :
    (ker g).localized' S p f = ker ((map p f f' g).extendScalarsOfIsLocalization p S) :=
  SetLike.ext (by apply SetLike.ext_iff.mp (f.ker_localizedMap_eq_localized₀_ker p f' g).symm)
/-
**LinearMap.ker_localizedMap_eq_localized'_ker** 是 Mathlib 中的一个定理，位于命名空间 `Linear
Map`。
形式化陈述：∀ {R : Type u_1} (S : Type u_2) {M : Type u_3} {N : Type u_4} [inst : Comm
Semiring R] [inst_1 : CommSemiring S]   [inst_2 : AddCommMonoid M] [inst_3 : Add
CommMonoid N] [inst_4 : _root_.Module R M] [inst_5 : _root_.Module R N]   [inst_
6 : Algebra R S] [inst_7 : _root_.Module S N] [inst_8 : IsScalarTower R S N] (p 
: Submonoid R)   [inst_9 : IsLocalization p S] (f : M →ₗ[R] N) [inst_10 : IsLoca
lizedModule p f] {P : Type u_5}   [inst_11 : AddCommMonoid P] [inst_12 : _root_.
Module R P] {Q : Type u_6} [inst_13 : AddCommMonoid Q]   [inst_14 : _root_.Modul
e R Q] [inst_15 : _root_.Module S Q] [IsScalarTower R S Q] (f' : P →ₗ[R] Q)   [i
nst_17 : IsLocalizedModule p f'] (g : M →ₗ[R] P),   ((IsLocalizedModule.map p f 
f') g).ker = Submodule.restrictScalars R (Submodule.localized' S p f g.ker)
参数：S : Type u_2；p : Submonoid R；f : M →ₗ[R] N；f' : P →ₗ[R] Q；g : M →ₗ[R] P；(IsLo
calizedModule.map p f f') g；Submodule.localized' S p f g.ker。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.restrictScalars.congr_simp`：∀ (S : Type u_1) {R : Type u_2} {M
 : Type u_3} [inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : Semiring S
]   [inst_3 : _root_.Modul…
· 使用定理 `LinearMap.localized'_ker_eq_ker_localizedMap`：∀ {R : Type u_1} (S : Type
 u_2) {M : Type u_3} {N : Type u_4} [inst : CommSemiring R] [inst_1 : CommSemiri
ng S]   [inst_2 : AddCommMonoid M]…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma ker_localizedMap_eq_localized'_ker (g : M →ₗ[R] P) :
    ker (map p f f' g) = ((ker g).localized' S p f).restrictScalars _ := by
  ext
  simp [localized'_ker_eq_ker_localizedMap S p f f']

/--
The canonical map from the kernel of `g` to the kernel of `g` localized at a submonoid.

This is a localization map by `LinearMap.toKerLocalized_isLocalizedModule`.
-/
@[simps!]
/-
**LinearMap.toKerIsLocalized** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：toKerIsLocalized (g : M ->ₗ[R] P) : ker g ->ₗ[R] ker (map p f f' g)
参数：g : M ->ₗ[R] P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map from the kernel of `g` to the kernel of `g` localized at a sub
monoid.

This is a localization map by `LinearMap.toKerLocalized_isLocalizedModule`.
-/
noncomputable def toKerIsLocalized (g : M →ₗ[R] P) :
    ker g →ₗ[R] ker (map p f f' g) :=
  f.restrict (fun x hx ↦ by simp [mem_ker, mem_ker.mp hx])

include S in
/-- The canonical map to the kernel of the localization of `g` is localizing.
In other words, localization commutes with kernels. -/
/-
**LinearMap.toKerLocalized_isLocalizedModule** 是 Mathlib 中的一个引理，位于命名空间 `LinearMa
p`。
形式化陈述：toKerLocalized_isLocalizedModule (g : M ->ₗ[R] P) : IsLocalizedModule p (t
oKerIsLocalized p f f' g)
参数：g : M ->ₗ[R] P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.localized'_ker_eq_ker_localizedMap`：∀ {R : Type u_1} (S : Type
 u_2) {M : Type u_3} {N : Type u_4} [inst : CommSemiring R] [inst_1 : CommSemiri
ng S]   [inst_2 : AddCommMonoid M]…
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …

--- 原说明 ---
The canonical map to the kernel of the localization of `g` is localizing.
In other words, localization commutes with kernels.
-/
lemma toKerLocalized_isLocalizedModule (g : M →ₗ[R] P) :
    IsLocalizedModule p (toKerIsLocalized p f f' g) :=
  let e : Submodule.localized' S p f (ker g) ≃ₗ[S]
      ker ((map p f f' g).extendScalarsOfIsLocalization p S) :=
    LinearEquiv.ofEq _ _ (localized'_ker_eq_ker_localizedMap S p f f' g)
  IsLocalizedModule.of_linearEquiv p (Submodule.toLocalized' S p f (ker g)) (e.restrictScalars R)
/-
**LinearMap.range_localizedMap_eq_localized** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma range_localizedMap_eq_localized₀_range (g : M →ₗ[R] P) :
    range (map p f f' g) = (range g).localized₀ p f' := by
  ext; simp [mem_localized₀, mem_range, (mk'_surjective p f).exists]

/-- Localization commutes with ranges. -/
/-
**LinearMap.localized'_range_eq_range_localizedMap** 是 Mathlib 中的一个定理，位于命名空间 `Li
nearMap`。
形式化陈述：∀ {R : Type u_1} (S : Type u_2) {M : Type u_3} {N : Type u_4} [inst : Comm
Semiring R] [inst_1 : CommSemiring S]   [inst_2 : AddCommMonoid M] [inst_3 : Add
CommMonoid N] [inst_4 : _root_.Module R M] [inst_5 : _root_.Module R N]   [inst_
6 : Algebra R S] [inst_7 : _root_.Module S N] [inst_8 : IsScalarTower R S N] (p 
: Submonoid R)   [inst_9 : IsLocalization p S] (f : M →ₗ[R] N) [inst_10 : IsLoca
lizedModule p f] {P : Type u_5}   [inst_11 : AddCommMonoid P] [inst_12 : _root_.
Module R P] {Q : Type u_6} [inst_13 : AddCommMonoid Q]   [inst_14 : _root_.Modul
e R Q] [inst_15 : _root_.Module S Q] [inst_16 : IsScalarTower R S Q] (f' : P →ₗ[
R] Q)   [inst_17 : IsLocalizedModule p f'] (g : M →ₗ[R] P),   Submodule.localize
d' S p f' g.range =     (LinearMap.extendScalarsOfIsLocalization p S ((IsLocaliz
edModule.map p f f') g)).range
参数：S : Type u_2；p : Submonoid R；f : M →ₗ[R] N；f' : P →ₗ[R] Q；g : M →ₗ[R] P；Linea
rMap.extendScalarsOfIsLocalization p S ((IsLocalizedModule.map p f f') g)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.ext_iff`：ext_iff : p = q ↔ forall x, x in p ↔ x in q
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LinearMap.range_localizedMap_eq_localized₀_range`：range_localizedMap_eq_
localized₀_range (g : M ->ₗ[R] P) : range (map p f f' g) = (range g).localized₀ 
p f'

--- 原说明 ---
Localization commutes with ranges.
-/
lemma localized'_range_eq_range_localizedMap (g : M →ₗ[R] P) :
    (range g).localized' S p f' = range ((map p f f' g).extendScalarsOfIsLocalization p S) :=
  SetLike.ext (by apply SetLike.ext_iff.mp (f.range_localizedMap_eq_localized₀_range p f' g).symm)
/-
**LinearMap.localizedMap_surjective_iff_subsingleton_localized_coker** 是 Mathlib
 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：localizedMap_surjective_iff_subsingleton_localized_coker {R M N : Type*} [
CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (S : Sub
monoid R) (φ : M ->ₗ[R] N) : Function.Surjective (LocalizedModule.map S φ) ↔ Sub
singleton (LocalizedModule S (N ⧸ φ.range))
参数：S : Submonoid R；φ : M ->ₗ[R] N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `OreLocalization.instIsScalarTower_1`：∀ {R : Type u_1} {M : Type u_3} {X 
: Type u_4} [inst : Monoid M] {S : Submonoid M} [inst_1 : OreLocalization.OreSet
 S]   [inst_2 : MulAction…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `LinearEquiv.restrictScalars_toLinearMap`：∀ (R : Type u_1) {S : Type u_4}
 {M : Type u_5} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring S]   [ins
t_2 : AddCommMonoid M] [inst_…
· 使用定理 `LinearMap.extendScalarsOfIsLocalizationEquiv_apply`：∀ {R : Type u_3} [in
st : CommSemiring R] (S : Submonoid R) (A : Type u_4) [inst_1 : CommSemiring A] 
  [inst_2 : Algebra R A] [inst_3 : IsLoc…
· 使用定理 `Equiv.subsingleton_congr`：subsingleton_congr (e : α ≃ β) : Subsingleton 
α ↔ Subsingleton β
· 使用定理 `LinearMap.localized'_range_eq_range_localizedMap`：∀ {R : Type u_1} (S : 
Type u_2) {M : Type u_3} {N : Type u_4} [inst : CommSemiring R] [inst_1 : CommSe
miring S]   [inst_2 : AddCommMonoid M]…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma localizedMap_surjective_iff_subsingleton_localized_coker {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (S : Submonoid R) (φ : M →ₗ[R] N) :
    Function.Surjective (LocalizedModule.map S φ) ↔
      Subsingleton (LocalizedModule S (N ⧸ φ.range)) := by
  simp [(localizedQuotientEquiv S φ.range).symm.subsingleton_congr,
    LinearMap.localized'_range_eq_range_localizedMap (Localization S) S
      (LocalizedModule.mkLinearMap S M) (LocalizedModule.mkLinearMap S N),
    LinearMap.range_eq_top, LocalizedModule.map, mapExtendScalars]

end LinearMap

