/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
module

public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.GroupTheory.MonoidLocalization.Maps
public import Mathlib.RingTheory.OreLocalization.Basic

/-!
# Localizations of commutative monoids with zeroes

-/

@[expose] public section

open Function

section CommMonoidWithZero

variable {M : Type*} [CommMonoidWithZero M] (S : Submonoid M) (N : Type*) [CommMonoidWithZero N]
  {P : Type*} [CommMonoidWithZero P]

namespace Submonoid

variable {S N}

/-- If `S` contains `0` then the localization at `S` is trivial. -/
/-
**Submonoid.LocalizationMap.subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.Lo
calizationMap`。
形式化陈述：∀ {M : Type u_1} [inst : CommMonoidWithZero M] {S : Submonoid M} {N : Type
 u_2} [inst_1 : CommMonoidWithZero N]   (f : S.LocalizationMap N), 0 ∈ S → Subsi
ngleton N
参数：f : S.LocalizationMap N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submonoid.LocalizationMap.mk'_sec`：∀ {M : Type u_1} [inst : CommMonoid M
] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (f : S.Localization
Map N) (z : N), f.mk' (…
· 使用定理 `Submonoid.LocalizationMap.eq`：∀ {M : Type u_1} [inst : CommMonoid M] {S 
: Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (f : S.LocalizationMap N
) {a₁ b₁ : M} {a₂ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `S` contains `0` then the localization at `S` is trivial.
-/
theorem LocalizationMap.subsingleton (f : LocalizationMap S N) (h : 0 ∈ S) : Subsingleton N where
  allEq a b := by
    rw [← f.mk'_sec a, ← f.mk'_sec b, f.eq]
    exact ⟨⟨0, h⟩, by simp only [zero_mul]⟩
/-
**Submonoid.LocalizationMap.subsingleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submonoi
d.LocalizationMap`。
形式化陈述：∀ {M : Type u_1} [inst : CommMonoidWithZero M] {S : Submonoid M} {N : Type
 u_2} [inst_1 : CommMonoidWithZero N]   (f : S.LocalizationMap N), Subsingleton 
N ↔ 0 ∈ S
参数：f : S.LocalizationMap N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.exists_of_eq`：exists_of_eq (f : LocalizationMa
p S N) {x y : M} : f x = f y -> exists c : S, c * x = c * y
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Submonoid.LocalizationMap.subsingleton`：∀ {M : Type u_1} [inst : CommMon
oidWithZero M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoidWithZero N] 
  (f : S.LocalizationMap N),…
-/
theorem LocalizationMap.subsingleton_iff (f : LocalizationMap S N) : Subsingleton N ↔ 0 ∈ S :=
  ⟨fun _ ↦ have ⟨c, eq⟩ := f.exists_of_eq (Subsingleton.elim (f 0) (f 1))
    by rw [mul_zero, mul_one] at eq; exact eq ▸ c.2, f.subsingleton⟩
/-
**Submonoid.LocalizationMap.nontrivial** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.Loca
lizationMap`。
形式化陈述：∀ {M : Type u_1} [inst : CommMonoidWithZero M] {S : Submonoid M} {N : Type
 u_2} [inst_1 : CommMonoidWithZero N]   (f : S.LocalizationMap N), 0 ∉ S → Nontr
ivial N
参数：f : S.LocalizationMap N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `not_subsingleton_iff_nontrivial`：not_subsingleton_iff_nontrivial : ¬Subs
ingleton α ↔ Nontrivial α
· 使用定理 `Submonoid.LocalizationMap.subsingleton_iff`：∀ {M : Type u_1} [inst : Com
mMonoidWithZero M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoidWithZero
 N]   (f : S.LocalizationMap N),…
-/
theorem LocalizationMap.nontrivial (f : LocalizationMap S N) (h : 0 ∉ S) : Nontrivial N := by
  rwa [← not_subsingleton_iff_nontrivial, f.subsingleton_iff]
/-
**Submonoid.LocalizationMap.map_zero** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.Locali
zationMap`。
形式化陈述：∀ {M : Type u_1} [inst : CommMonoidWithZero M] {S : Submonoid M} {N : Type
 u_2} [inst_1 : CommMonoidWithZero N]   (f : S.LocalizationMap N), f 0 = 0
参数：f : S.LocalizationMap N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.surj`：surj (f : LocalizationMap S N) (z : N) :
 exists x : M × S, z * f x.2 = f x.1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `Submonoid.LocalizationMap.instMonoidHomClass`：∀ {M : Type u_1} [inst : C
ommMonoid M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N],   MonoidH
omClass (S.LocalizationMap N) M N
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
protected theorem LocalizationMap.map_zero (f : LocalizationMap S N) : f 0 = 0 := by
  have ⟨ms, eq⟩ := f.surj 0
  rw [← zero_mul, map_mul, ← eq, zero_mul, mul_zero]
/-
**Submonoid.IsLocalizationMap.map_zero** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.IsLo
calizationMap`。
形式化陈述：∀ {M : Type u_1} [inst : CommMonoidWithZero M] {S : Submonoid M} {N : Type
 u_2} [inst_1 : CommMonoidWithZero N]   {F : Type u_4} [inst_2 : FunLike F M N] 
[MulHomClass F M N] {f : F}, S.IsLocalizationMap ⇑f → f 0 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.map_zero`：∀ {M : Type u_1} [inst : CommMonoidW
ithZero M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoidWithZero N]   (f
 : S.LocalizationMap N),…
-/
protected theorem IsLocalizationMap.map_zero {F} [FunLike F M N] [MulHomClass F M N] {f : F}
    (hf : IsLocalizationMap S f) : f 0 = 0 :=
  LocalizationMap.map_zero ⟨MulHomClass.toMulHom f, hf⟩
/-
**Submonoid.** 是 Mathlib 中的一个实例，位于命名空间 `Submonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MonoidWithZeroHomClass (LocalizationMap S N) M N where
  map_zero f := by
    have ⟨ms, eq⟩ := f.surj 0
    rw [← zero_mul, map_mul, ← eq, zero_mul, mul_zero]

end Submonoid

namespace Localization

variable {S}

/-
**Localization.mk_zero** 是 Mathlib 中的一个定理，位于命名空间 `Localization`。
形式化陈述：mk_zero (x : S) : mk 0 (x : S) = 0
参数：x : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OreLocalization.zero_oreDiv'`：zero_oreDiv' (s : S) : (0 : R) /ₒ s = 0
-/
theorem mk_zero (x : S) : mk 0 (x : S) = 0 := OreLocalization.zero_oreDiv' _
/-
**Localization.** 是 Mathlib 中的一个实例，位于命名空间 `Localization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CommMonoidWithZero (Localization S) where
  zero_mul := fun x ↦ Localization.induction_on x fun y => by
    simp only [← Localization.mk_zero y.2, mk_mul, mk_eq_mk_iff, mul_zero, zero_mul, r_of_eq]
  mul_zero := fun x ↦ Localization.induction_on x fun y => by
    simp only [← Localization.mk_zero y.2, mk_mul, mk_eq_mk_iff, mul_zero, r_of_eq]
/-
**Localization.liftOn_zero** 是 Mathlib 中的一个定理，位于命名空间 `Localization`。
形式化陈述：liftOn_zero {p : Type*} (f : M -> S -> p) (H) : liftOn 0 f H = f 0 1
参数：f : M -> S -> p；H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Localization.mk_zero`：mk_zero (x : S) : mk 0 (x : S) = 0
· 使用定理 `Localization.liftOn_mk`：liftOn_mk {p : Sort u} (f : M -> S -> p) (H) (a 
: M) (b : S) : liftOn (mk a b) f H = f a b
-/
theorem liftOn_zero {p : Type*} (f : M → S → p) (H) : liftOn 0 f H = f 0 1 := by
  rw [← mk_zero 1, liftOn_mk]

end Localization

variable {S N}

namespace Submonoid

@[simp]
/-
**Submonoid.LocalizationMap.sec_zero_fst** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.Lo
calizationMap`。
形式化陈述：∀ {M : Type u_1} [inst : CommMonoidWithZero M] {S : Submonoid M} {N : Type
 u_2} [inst_1 : CommMonoidWithZero N]   {f : S.LocalizationMap N}, f (f.sec 0).1
 = 0
参数：f.sec 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submonoid.LocalizationMap.sec_spec'`：sec_spec' {f : LocalizationMap S N}
 (z : N) : f (f.sec z).1 = f (f.sec z).2 * z
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem LocalizationMap.sec_zero_fst {f : LocalizationMap S N} : f (f.sec 0).fst = 0 := by
  rw [LocalizationMap.sec_spec', mul_zero]

namespace LocalizationMap

/-- Given a Localization map `f : M →*₀ N` for a Submonoid `S ⊆ M` and a map of
`CommMonoidWithZero`s `g : M →*₀ P` such that `g y` is invertible for all `y : S`, the
homomorphism induced from `N` to `P` sending `z : N` to `g x * (g y)⁻¹`, where `(x, y) : M × S`
are such that `z = f x * (f y)⁻¹`. -/
/-
**Submonoid.LocalizationMap.lift** 是 Mathlib 中的一个定义，位于命名空间 `Submonoid.Localizati
onMap`。
形式化陈述：lift : N ->* P where toFun z
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a Localization map `f : M →*₀ N` for a Submonoid `S ⊆ M` and a map of
`CommMonoidWithZero`s `g : M →*₀ P` such that `g y` is invertible for all `y : S
`, the
homomorphism induced from `N` to `P` sending `z : N` to `g x * (g y)⁻¹`, where `
(x, y) : M × S`
are such that `z = f x * (f y)⁻¹`.
-/
noncomputable def lift₀ (f : LocalizationMap S N) (g : M →*₀ P)
    (hg : ∀ y : S, IsUnit (g y)) : N →*₀ P :=
  { @LocalizationMap.lift _ _ _ _ _ _ _ f g.toMonoidHom hg with
    map_zero' := by
      dsimp only [OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe]
      rw [LocalizationMap.lift_spec f hg 0 0, mul_zero, ← map_zero g, ← g.toMonoidHom_coe]
      refine f.eq_of_eq hg ?_
      rw [LocalizationMap.sec_zero_fst]
      exact (map_zero f).symm }
/-
**Submonoid.LocalizationMap.lift** 是 Mathlib 中的一个定义，位于命名空间 `Submonoid.Localizati
onMap`。
形式化陈述：lift : N ->* P where toFun z
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma lift₀_def (f : LocalizationMap S N) (g : M →*₀ P) (hg : ∀ y : S, IsUnit (g y)) :
    ⇑(f.lift₀ g hg) = f.lift (g := g) hg := rfl
/-
**Submonoid.LocalizationMap.lift** 是 Mathlib 中的一个定义，位于命名空间 `Submonoid.Localizati
onMap`。
形式化陈述：lift : N ->* P where toFun z
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma lift₀_apply (f : LocalizationMap S N) (g : M →*₀ P) (hg : ∀ y : S, IsUnit (g y)) (x) :
    f.lift₀ g hg x = g (f.sec x).1 * (IsUnit.liftRight (g.domRestrict S) hg (f.sec x).2)⁻¹ := rfl

/-- Given a Localization map `f : M →*₀ N` for a Submonoid `S ⊆ M`,
if `M` is a cancellative monoid with zero, and all elements of `S` are
regular, then N is a cancellative monoid with zero. -/
/-
**Submonoid.LocalizationMap.isCancelMulZero** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid
.LocalizationMap`。
形式化陈述：isCancelMulZero (f : LocalizationMap S N) [IsCancelMulZero M] : IsCancelMu
lZero N
参数：f : LocalizationMap S N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Commute.isRegular_iff`：Commute.isRegular_iff {a : R} (ca : forall b, Com
mute a b) : IsRegular a ↔ IsLeftRegular a
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Commute.isRightRegular_iff`：∀ {R : Type u_1} [inst : Mul R] {a : R}, (∀ 
(b : R), Commute a b) → (IsRightRegular a ↔ IsLeftRegular a)
· 使用定理 `Submonoid.LocalizationMap.surj`：surj (f : LocalizationMap S N) (z : N) :
 exists x : M × S, z * f x.2 = f x.1
· 使用定理 `IsRightRegular.of_mul`：IsRightRegular.of_mul (ab : IsRightRegular (b * a
)) : IsRightRegular b
· 使用定理 `IsRegular.right`：∀ {R : Type u_1} [inst : Mul R] {c : R}, IsRegular c → 
IsRightRegular c
· 使用定理 `Submonoid.LocalizationMap.map_isRegular`：∀ {M : Type u_1} {N : Type u_2}
 [inst : CommMonoid M] {S : Submonoid M} [inst_1 : CommMonoid N]   (f : S.Locali
zationMap N) {m : M}, IsRegul…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isCancelMulZero_iff_forall_isRegular`：isCancelMulZero_iff_forall_isRegul
ar {M₀} [Mul M₀] [Zero M₀] : IsCancelMulZero M₀ ↔ forall {a : M₀}, a != 0 -> IsR
egular a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsUnit.mul_left_eq_zero`：mul_left_eq_zero {a b : M₀} (hb : IsUnit b) : a
 * b = 0 ↔ a = 0
· 使用定理 `Submonoid.LocalizationMap.map_units`：map_units (f : LocalizationMap S N)
 (y : S) : IsUnit (f y)
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `Submonoid.instMonoidWithZeroHomClassLocalizationMap`：∀ {M : Type u_1} [i
nst : CommMonoidWithZero M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoi
dWithZero N],   MonoidWithZeroHomClass (S…

--- 原说明 ---
Given a Localization map `f : M →*₀ N` for a Submonoid `S ⊆ M`,
if `M` is a cancellative monoid with zero, and all elements of `S` are
regular, then N is a cancellative monoid with zero.
-/
theorem isCancelMulZero (f : LocalizationMap S N) [IsCancelMulZero M] : IsCancelMulZero N := by
  simp_rw [isCancelMulZero_iff_forall_isRegular, Commute.isRegular_iff (Commute.all _),
    ← Commute.isRightRegular_iff (Commute.all _)]
  intro n hn
  have ⟨ms, eq⟩ := f.surj n
  refine (eq ▸ f.map_isRegular (isCancelMulZero_iff_forall_isRegular.mp ‹_› ?_)).2.of_mul
  refine fun h ↦ hn ?_
  rwa [h, map_zero, (f.map_units _).mul_left_eq_zero] at eq
/-
**Submonoid.LocalizationMap.map_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid
.LocalizationMap`。
形式化陈述：map_eq_zero_iff (f : LocalizationMap S N) {m : M} : f m = 0 ↔ exists s : S
, s * m = 0
参数：f : LocalizationMap S N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submonoid.LocalizationMap.map_zero`：∀ {M : Type u_1} [inst : CommMonoidW
ithZero M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoidWithZero N]   (f
 : S.LocalizationMap N),…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem map_eq_zero_iff (f : LocalizationMap S N) {m : M} : f m = 0 ↔ ∃ s : S, s * m = 0 := by
  simp_rw [← f.map_zero, eq_iff_exists, mul_zero]
/-
**Submonoid.LocalizationMap.mk'_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid
.LocalizationMap`。
形式化陈述：∀ {M : Type u_1} [inst : CommMonoidWithZero M] {S : Submonoid M} {N : Type
 u_2} [inst_1 : CommMonoidWithZero N]   (f : S.LocalizationMap N) (m : M) (s : ↥
S), f.mk' m s = 0 ↔ ∃ s, ↑s * m = 0
参数：f : S.LocalizationMap N；m : M；s : ↥S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsUnit.mul_left_inj`：mul_left_inj (h : IsUnit a) : b * a = c * a ↔ b = c
· 使用定理 `Submonoid.LocalizationMap.map_units`：map_units (f : LocalizationMap S N)
 (y : S) : IsUnit (f y)
· 使用定理 `Submonoid.LocalizationMap.mk'_spec`：∀ {M : Type u_1} [inst : CommMonoid 
M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (f : S.Localizatio
nMap N) (x : M) (y : ↥S)…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Submonoid.LocalizationMap.map_eq_zero_iff`：map_eq_zero_iff (f : Localiza
tionMap S N) {m : M} : f m = 0 ↔ exists s : S, s * m = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mk'_eq_zero_iff (f : LocalizationMap S N) (m : M) (s : S) :
    f.mk' m s = 0 ↔ ∃ s : S, s * m = 0 := by
  rw [← (f.map_units s).mul_left_inj, mk'_spec, zero_mul, map_eq_zero_iff]
/-
**Submonoid.LocalizationMap.mk'_zero** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.Locali
zationMap`。
形式化陈述：∀ {M : Type u_1} [inst : CommMonoidWithZero M] {S : Submonoid M} {N : Type
 u_2} [inst_1 : CommMonoidWithZero N]   (f : S.LocalizationMap N) (s : ↥S), f.mk
' 0 s = 0
参数：f : S.LocalizationMap N；s : ↥S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Submonoid.LocalizationMap.eq_mk'_iff_mul_eq`：∀ {M : Type u_1} [inst : Co
mmMonoid M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (f : S.Lo
calizationMap N) {x : M} {y : ↥S}…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Submonoid.LocalizationMap.map_zero`：∀ {M : Type u_1} [inst : CommMonoidW
ithZero M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoidWithZero N]   (f
 : S.LocalizationMap N),…
-/
@[simp] theorem mk'_zero (f : LocalizationMap S N) (s : S) : f.mk' 0 s = 0 := by
  rw [eq_comm, eq_mk'_iff_mul_eq, zero_mul, f.map_zero]
/-
**Submonoid.LocalizationMap.nonZeroDivisors_le_comap** 是 Mathlib 中的一个定理，位于命名空间 `
Submonoid.LocalizationMap`。
形式化陈述：nonZeroDivisors_le_comap (f : LocalizationMap S N) : nonZeroDivisors M <= 
(nonZeroDivisors N).comap f
参数：f : LocalizationMap S N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.instMonoidHomClass`：∀ {M : Type u_1} [inst : C
ommMonoid M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N],   MonoidH
omClass (S.LocalizationMap N) M N
· 使用定理 `Submonoid.LocalizationMap.surj`：surj (f : LocalizationMap S N) (z : N) :
 exists x : M × S, z * f x.2 = f x.1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsUnit.mul_left_eq_zero`：mul_left_eq_zero {a b : M₀} (hb : IsUnit b) : a
 * b = 0 ↔ a = 0
· 使用定理 `Submonoid.LocalizationMap.map_units`：map_units (f : LocalizationMap S N)
 (y : S) : IsUnit (f y)
· 使用定理 `Submonoid.LocalizationMap.map_eq_zero_iff`：map_eq_zero_iff (f : Localiza
tionMap S N) {m : M} : f m = 0 ↔ exists s : S, s * m = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_right_mem_nonZeroDivisorsRight_eq_zero_iff`：mul_right_mem_nonZeroDiv
isorsRight_eq_zero_iff (hr : r in nonZeroDivisorsRight M₀) : x * r = 0 ↔ x = 0
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `mul_right_comm`：mul_right_comm (a b c : G) : a * b * c = a * c * b
· 使用引理 `nonZeroDivisorsRight_eq_nonZeroDivisors`：nonZeroDivisorsRight_eq_nonZero
Divisors : nonZeroDivisorsRight M₀ = nonZeroDivisors M₀
-/
theorem nonZeroDivisors_le_comap (f : LocalizationMap S N) :
    nonZeroDivisors M ≤ (nonZeroDivisors N).comap f := by
  refine fun m hm ↦ nonZeroDivisorsRight_eq_nonZeroDivisors (M₀ := N) ▸ fun n h0 ↦ ?_
  have ⟨ms, eq⟩ := f.surj n
  rw [← (f.map_units ms.2).mul_left_eq_zero, mul_right_comm, eq, ← map_mul, map_eq_zero_iff] at h0
  simp_rw [← mul_assoc, mul_right_mem_nonZeroDivisorsRight_eq_zero_iff hm.2] at h0
  rwa [← (f.map_units ms.2).mul_left_eq_zero, eq, map_eq_zero_iff]
/-
**Submonoid.LocalizationMap.map_nonZeroDivisors_le** 是 Mathlib 中的一个定理，位于命名空间 `Su
bmonoid.LocalizationMap`。
形式化陈述：map_nonZeroDivisors_le (f : LocalizationMap S N) : (nonZeroDivisors M).map
 f <= nonZeroDivisors N
参数：f : LocalizationMap S N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submonoid.LocalizationMap.instMonoidHomClass`：∀ {M : Type u_1} [inst : C
ommMonoid M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N],   MonoidH
omClass (S.LocalizationMap N) M N
· 使用定理 `Submonoid.map_le_iff_le_comap`：map_le_iff_le_comap {f : F} {S : Submonoi
d M} {T : Submonoid N} : S.map f <= T ↔ S <= T.comap f
· 使用定理 `Submonoid.LocalizationMap.nonZeroDivisors_le_comap`：nonZeroDivisors_le_c
omap (f : LocalizationMap S N) : nonZeroDivisors M <= (nonZeroDivisors N).comap 
f
-/
theorem map_nonZeroDivisors_le (f : LocalizationMap S N) :
    (nonZeroDivisors M).map f ≤ nonZeroDivisors N :=
  map_le_iff_le_comap.mpr f.nonZeroDivisors_le_comap
/-
**Submonoid.LocalizationMap.noZeroDivisors** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.
LocalizationMap`。
形式化陈述：noZeroDivisors (f : LocalizationMap S N) [NoZeroDivisors M] : NoZeroDiviso
rs N
参数：f : LocalizationMap S N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `noZeroDivisors_iff_forall_mem_nonZeroDivisors`：noZeroDivisors_iff_forall
_mem_nonZeroDivisors : NoZeroDivisors M₀ ↔ forall x : M₀, x != 0 -> x in M₀⁰
· 使用定理 `Submonoid.LocalizationMap.surj`：surj (f : LocalizationMap S N) (z : N) :
 exists x : M × S, z * f x.2 = f x.1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsUnit.mul_left_eq_zero`：mul_left_eq_zero {a b : M₀} (hb : IsUnit b) : a
 * b = 0 ↔ a = 0
· 使用定理 `Submonoid.LocalizationMap.map_units`：map_units (f : LocalizationMap S N)
 (y : S) : IsUnit (f y)
· 使用定理 `Submonoid.LocalizationMap.map_zero`：∀ {M : Type u_1} [inst : CommMonoidW
ithZero M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoidWithZero N]   (f
 : S.LocalizationMap N),…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `mul_mem_nonZeroDivisors`：mul_mem_nonZeroDivisors : a * b in M₀⁰ ↔ a in M
₀⁰ ∧ b in M₀⁰ where mp h
· 使用定理 `Submonoid.LocalizationMap.map_nonZeroDivisors_le`：map_nonZeroDivisors_le
 (f : LocalizationMap S N) : (nonZeroDivisors M).map f <= nonZeroDivisors N
· 使用定理 `mem_nonZeroDivisors_of_ne_zero`：mem_nonZeroDivisors_of_ne_zero (hx : x !
= 0) : x in M₀⁰
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem noZeroDivisors (f : LocalizationMap S N) [NoZeroDivisors M] : NoZeroDivisors N := by
  refine noZeroDivisors_iff_forall_mem_nonZeroDivisors.mpr fun n hn ↦ ?_
  have ⟨ms, eq⟩ := f.surj n
  have hs : ms.1 ≠ 0 := fun h ↦ hn (by rwa [h, f.map_zero, (f.map_units _).mul_left_eq_zero] at eq)
  exact And.left <| mul_mem_nonZeroDivisors.mp
    (eq ▸ f.map_nonZeroDivisors_le ⟨_, mem_nonZeroDivisors_of_ne_zero hs, rfl⟩)

end LocalizationMap

end Submonoid

end CommMonoidWithZero

