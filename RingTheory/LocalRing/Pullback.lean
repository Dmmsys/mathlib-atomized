/-
Copyright (c) 2026 Bingyu Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

module

public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

import Mathlib.Algebra.Ring.Subring.Units
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Local Ring Properties of Equalizers and Pullbacks

In this file we provide basic lemmas for the equalizers the pullbacks and of ring homomorphisms
and algebra homomorphisms. We show that they preserve the property of being a local ring under
suitable conditions.

## Main definitions

* `RingHom.pullback`: The pullback of two ring homomorphisms `f : R →+* T` and `g : S →+* T`,
  defined as the subring of `R × S` consisting of pairs `(r, s)` such that `f r = g s`.

* `RingHom.pullbackFst`, `RingHom.pullbackSnd`: The canonical projection maps from the
  pullback to `R` and `S`.

## Main results

* `RingHom.isLocalRing_eqLocus`: The equalizer of two ring homomorphisms from a local
  ring is again a local ring.

* `RingHom.isLocalRing_pullback`: The pullback of `f : R →+* T` and `g : S →+* T` is a
  local ring, provided that `R` is a local ring and `g` is a local homomorphism.

-/

@[expose] public section

namespace RingHom

variable {R S T : Type*} [Ring R] [Ring S] [Semiring T]

/-
**RingHom.isLocalRing_eqLocus** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：isLocalRing_eqLocus [IsLocalRing R] (f g : R ->+* T) : IsLocalRing (f.eqLo
cus g)
参数：f g : R ->+* T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.domain_isLocalRing`：RingHom.domain_isLocalRing [IsLocalRing S] (
f : R ->+* S) [IsLocalHom f] : IsLocalRing R where toNontrivial
· 使用定理 `RingHom.instIsLocalHomSubtypeMemSubringEqLocusSubtype`：∀ {R : Type u_1} 
{T : Type u_2} [inst : Semiring T] [inst_1 : Ring R] (f g : R →+* T), IsLocalHom
 (f.eqLocus g).subtype
-/
theorem isLocalRing_eqLocus [IsLocalRing R] (f g : R →+* T) : IsLocalRing (f.eqLocus g) :=
  (f.eqLocus g).subtype.domain_isLocalRing

/-- The subring of pairs `(r, s) : R × S` such that `f r = g s`, i.e.,
  the pullback of `f : R →+* T` and `g : S →+* T` as a subring of `R × S`. -/
/-
**RingHom.pullback** 是 Mathlib 中的一个缩写定义，位于命名空间 `RingHom`。
形式化陈述：pullback (f : R ->+* T) (g : S ->+* T) : Subring (R × S)
参数：f : R ->+* T；g : S ->+* T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subring of pairs `(r, s) : R × S` such that `f r = g s`, i.e.,
  the pullback of `f : R →+* T` and `g : S →+* T` as a subring of `R × S`.
-/
abbrev pullback (f : R →+* T) (g : S →+* T) : Subring (R × S) :=
  (f.comp (RingHom.fst R S)).eqLocus <| g.comp (RingHom.snd R S)

/-- The first projection from the pullback of `f : R →+* T` and `g : S →+* T` to `R`. -/
/-
**RingHom.pullbackFst** 是 Mathlib 中的一个缩写定义，位于命名空间 `RingHom`。
形式化陈述：pullbackFst (f : R ->+* T) (g : S ->+* T) : f.pullback g ->+* R
参数：f : R ->+* T；g : S ->+* T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The first projection from the pullback of `f : R →+* T` and `g : S →+* T` to `R`
.
-/
abbrev pullbackFst (f : R →+* T) (g : S →+* T) : f.pullback g →+* R :=
  (RingHom.fst R S).comp (RingHom.pullback f g).subtype

/-- The second projection from the pullback of `f : R →+* T` and `g : S →+* T` to `S`. -/
/-
**RingHom.pullbackSnd** 是 Mathlib 中的一个缩写定义，位于命名空间 `RingHom`。
形式化陈述：pullbackSnd (f : R ->+* T) (g : S ->+* T) : f.pullback g ->+* S
参数：f : R ->+* T；g : S ->+* T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The second projection from the pullback of `f : R →+* T` and `g : S →+* T` to `S
`.
-/
abbrev pullbackSnd (f : R →+* T) (g : S →+* T) : f.pullback g →+* S :=
  (RingHom.snd R S).comp (f.pullback g).subtype
/-
**RingHom.pullback_comm_sq** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：pullback_comm_sq (f : R ->+* T) (g : S ->+* T) : f.comp (f.pullbackFst g) 
= g.comp (f.pullbackSnd g)
参数：f : R ->+* T；g : S ->+* T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem pullback_comm_sq (f : R →+* T) (g : S →+* T) :
    f.comp (f.pullbackFst g) = g.comp (f.pullbackSnd g) :=
  ext fun x ↦ x.prop

set_option backward.isDefEq.respectTransparency.types false in
/-
**RingHom.isUnit_pullback_mk_iff** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：isUnit_pullback_mk_iff (f : R ->+* T) (g : S ->+* T) {a : R × S} (a_in : a
 in f.pullback g) : IsUnit (⟨a, a_in⟩ : f.pullback g) ↔ IsUnit a.1 ∧ IsUnit a.2
参数：f : R ->+* T；g : S ->+* T；a_in : a in f.pullback g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.isUnit_eqLocus_mk_iff`：isUnit_eqLocus_mk_iff [Ring R] (f g : R -
>+* T) {r : R} (hr : f r = g r) : IsUnit (⟨r, hr⟩ : f.eqLocus g) ↔ IsUnit r
· 使用定理 `Prod.isUnit_iff`：∀ {M : Type u_3} {N : Type u_4} [inst : Monoid M] [inst
_1 : Monoid N] {x : M × N}, IsUnit x ↔ IsUnit x.1 ∧ IsUnit x.2
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isUnit_pullback_mk_iff (f : R →+* T) (g : S →+* T) {a : R × S} (a_in : a ∈ f.pullback g) :
    IsUnit (⟨a, a_in⟩ : f.pullback g) ↔ IsUnit a.1 ∧ IsUnit a.2 := by
  rw [isUnit_eqLocus_mk_iff, Prod.isUnit_iff]
/-
**RingHom.isLocalHom_pullbackFst** 是 Mathlib 中的一个实例，位于命名空间 `RingHom`。
形式化陈述：isLocalHom_pullbackFst (f : R ->+* T) (g : S ->+* T) [IsLocalHom g] : IsLo
calHom (f.pullbackFst g) where map_nonunit
参数：f : R ->+* T；g : S ->+* T。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `RingHom.isUnit_pullback_mk_iff`：isUnit_pullback_mk_iff (f : R ->+* T) (g
 : S ->+* T) {a : R × S} (a_in : a in f.pullback g) : IsUnit (⟨a, a_in⟩ : f.pull
back g) ↔ IsUnit a.1…
· 使用定理 `isUnit_of_map_unit`：∀ {R : Type u_2} {S : Type u_3} {F : Type u_5} [inst
 : Monoid R] [inst_1 : Monoid S] [inst_2 : FunLike F R S] (f : F)   [IsLocalHom 
f] (a : …
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
instance isLocalHom_pullbackFst (f : R →+* T) (g : S →+* T) [IsLocalHom g] :
    IsLocalHom (f.pullbackFst g) where
  map_nonunit := fun ⟨⟨_, _⟩, h_in⟩ ha ↦
    (isUnit_pullback_mk_iff f g h_in).mpr ⟨ha, isUnit_of_map_unit g _ (h_in ▸ ha.map f)⟩
/-
**RingHom.isLocalHom_pullbackSnd** 是 Mathlib 中的一个实例，位于命名空间 `RingHom`。
形式化陈述：isLocalHom_pullbackSnd (f : R ->+* T) (g : S ->+* T) [IsLocalHom f] : IsLo
calHom (f.pullbackSnd g) where map_nonunit
参数：f : R ->+* T；g : S ->+* T。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `RingHom.isUnit_pullback_mk_iff`：isUnit_pullback_mk_iff (f : R ->+* T) (g
 : S ->+* T) {a : R × S} (a_in : a in f.pullback g) : IsUnit (⟨a, a_in⟩ : f.pull
back g) ↔ IsUnit a.1…
· 使用定理 `isUnit_of_map_unit`：∀ {R : Type u_2} {S : Type u_3} {F : Type u_5} [inst
 : Monoid R] [inst_1 : Monoid S] [inst_2 : FunLike F R S] (f : F)   [IsLocalHom 
f] (a : …
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
instance isLocalHom_pullbackSnd (f : R →+* T) (g : S →+* T) [IsLocalHom f] :
    IsLocalHom (f.pullbackSnd g) where
  map_nonunit := fun ⟨⟨_, _⟩, h_in⟩ ha ↦
    (isUnit_pullback_mk_iff f g h_in).mpr ⟨isUnit_of_map_unit f _ (h_in.symm ▸ ha.map g), ha⟩
/-
**RingHom.surjective_pullbackFst_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `RingHo
m`。
形式化陈述：surjective_pullbackFst_of_surjective (f : R ->+* T) (g : S ->+* T) (h : Fu
nction.Surjective g) : Function.Surjective (f.pullbackFst g)
参数：f : R ->+* T；g : S ->+* T；h : Function.Surjective g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem surjective_pullbackFst_of_surjective (f : R →+* T) (g : S →+* T)
    (h : Function.Surjective g) : Function.Surjective (f.pullbackFst g) :=
  fun r ↦ by simpa [eq_comm] using h (f r)
/-
**RingHom.surjective_pullbackSnd_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `RingHo
m`。
形式化陈述：surjective_pullbackSnd_of_surjective (f : R ->+* T) (g : S ->+* T) (h : Fu
nction.Surjective f) : Function.Surjective (f.pullbackSnd g)
参数：f : R ->+* T；g : S ->+* T；h : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem surjective_pullbackSnd_of_surjective (f : R →+* T) (g : S →+* T)
    (h : Function.Surjective f) : Function.Surjective (f.pullbackSnd g) :=
  fun s ↦ by simpa [eq_comm] using h (g s)
/-
**RingHom.map_pullbackSnd_ker_pullbackFst_eq** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`
。
形式化陈述：map_pullbackSnd_ker_pullbackFst_eq (f : R ->+* T) (g : S ->+* T) : Ideal.m
ap (f.pullbackSnd g) (RingHom.ker (f.pullbackFst g)) = RingHom.ker g
参数：f : R ->+* T；g : S ->+* T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.map_le_iff_le_comap`：map_le_iff_le_comap [RingHomClass F R S] : ma
p f I <= K ↔ I <= comap f K
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ideal.mem_map_of_mem`：mem_map_of_mem (f : F) {I : Ideal R} {x : R} (h : 
x in I) : f x in map f I
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_pullbackSnd_ker_pullbackFst_eq (f : R →+* T) (g : S →+* T) :
    Ideal.map (f.pullbackSnd g) (RingHom.ker (f.pullbackFst g)) = RingHom.ker g := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    rintro ⟨⟨_, _⟩, h⟩
    simp at h ⊢; grind
  · intro s hs
    exact Ideal.mem_map_of_mem (f.pullbackSnd g) (x := ⟨(0, s), by simpa using hs.symm⟩)
      (I := RingHom.ker (f.pullbackFst g)) (by simp)
/-
**RingHom.isLocalRing_pullback** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：isLocalRing_pullback [IsLocalRing R] (f : R ->+* T) (g : S ->+* T) [IsLoca
lHom g] : IsLocalRing (f.pullback g)
参数：f : R ->+* T；g : S ->+* T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.domain_isLocalRing`：RingHom.domain_isLocalRing [IsLocalRing S] (
f : R ->+* S) [IsLocalHom f] : IsLocalRing R where toNontrivial
-/
theorem isLocalRing_pullback [IsLocalRing R] (f : R →+* T) (g : S →+* T) [IsLocalHom g] :
    IsLocalRing (f.pullback g) := (f.pullbackFst g).domain_isLocalRing

end RingHom

namespace AlgHom

variable {R A B C : Type*} [CommSemiring R]

section Semiring

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

/-- The subalgebra of pairs `(a, b) : A × B` such that `f a = g b`, i.e.,
  the pullback of f and g as a subalgebra of A × B. -/
/-
**AlgHom.pullback** 是 Mathlib 中的一个缩写定义，位于命名空间 `AlgHom`。
形式化陈述：pullback (f : A ->ₐ[R] C) (g : B ->ₐ[R] C) : Subalgebra R (A × B)
参数：f : A ->ₐ[R] C；g : B ->ₐ[R] C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subalgebra of pairs `(a, b) : A × B` such that `f a = g b`, i.e.,
  the pullback of f and g as a subalgebra of A × B.
-/
abbrev pullback (f : A →ₐ[R] C) (g : B →ₐ[R] C) : Subalgebra R (A × B) := equalizer
  (f.comp (fst R A B)) (g.comp (snd R A B))

/-- The first projection from the pullback of `f` and `g` to `A`. -/
/-
**AlgHom.pullbackFst** 是 Mathlib 中的一个缩写定义，位于命名空间 `AlgHom`。
形式化陈述：pullbackFst (f : A ->ₐ[R] C) (g : B ->ₐ[R] C) : pullback f g ->ₐ[R] A
参数：f : A ->ₐ[R] C；g : B ->ₐ[R] C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The first projection from the pullback of `f` and `g` to `A`.
-/
abbrev pullbackFst (f : A →ₐ[R] C) (g : B →ₐ[R] C) : pullback f g →ₐ[R] A :=
  (fst R A B).comp (pullback f g).val

/-- The second projection from the pullback of `f` and `g` to `B`. -/
/-
**AlgHom.pullbackSnd** 是 Mathlib 中的一个缩写定义，位于命名空间 `AlgHom`。
形式化陈述：pullbackSnd (f : A ->ₐ[R] C) (g : B ->ₐ[R] C) : pullback f g ->ₐ[R] B
参数：f : A ->ₐ[R] C；g : B ->ₐ[R] C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The second projection from the pullback of `f` and `g` to `B`.
-/
abbrev pullbackSnd (f : A →ₐ[R] C) (g : B →ₐ[R] C) : pullback f g →ₐ[R] B :=
  (snd R A B).comp (pullback f g).val
/-
**AlgHom.pullback_comm_sq** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：pullback_comm_sq (f : A ->ₐ[R] C) (g : B ->ₐ[R] C) : f.comp (pullbackFst f
 g) = g.comp (pullbackSnd f g)
参数：f : A ->ₐ[R] C；g : B ->ₐ[R] C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem pullback_comm_sq (f : A →ₐ[R] C) (g : B →ₐ[R] C) :
    f.comp (pullbackFst f g) = g.comp (pullbackSnd f g) :=
  AlgHom.ext fun x ↦ x.prop

end Semiring

section Ring

variable [Ring A] [Algebra R A] [Ring B] [Algebra R B] [Semiring C] [Algebra R C]

/-
**AlgHom.isUnit_pullback_mk_iff** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：isUnit_pullback_mk_iff (f : A ->ₐ[R] C) (g : B ->ₐ[R] C) {a : A × B} (a_in
 : a in f.pullback g) : IsUnit (⟨a, a_in⟩ : f.pullback g) ↔ IsUnit a.1 ∧ IsUnit 
a.2
参数：f : A ->ₐ[R] C；g : B ->ₐ[R] C；a_in : a in f.pullback g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.isUnit_pullback_mk_iff`：isUnit_pullback_mk_iff (f : R ->+* T) (g
 : S ->+* T) {a : R × S} (a_in : a in f.pullback g) : IsUnit (⟨a, a_in⟩ : f.pull
back g) ↔ IsUnit a.1…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
-/
theorem isUnit_pullback_mk_iff (f : A →ₐ[R] C) (g : B →ₐ[R] C) {a : A × B}
    (a_in : a ∈ f.pullback g) : IsUnit (⟨a, a_in⟩ : f.pullback g) ↔
      IsUnit a.1 ∧ IsUnit a.2 :=
  RingHom.isUnit_pullback_mk_iff (f : A →+* C) (g : B →+* C) a_in
/-
**AlgHom.surjective_pullbackFst_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`
。
形式化陈述：surjective_pullbackFst_of_surjective (f : A ->ₐ[R] C) (g : B ->ₐ[R] C) (h 
: Function.Surjective g) : Function.Surjective (pullbackFst f g)
参数：f : A ->ₐ[R] C；g : B ->ₐ[R] C；h : Function.Surjective g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.surjective_pullbackFst_of_surjective`：surjective_pullbackFst_of_
surjective (f : R ->+* T) (g : S ->+* T) (h : Function.Surjective g) : Function.
Surjective (f.pullbackFst g)
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
-/
theorem surjective_pullbackFst_of_surjective (f : A →ₐ[R] C) (g : B →ₐ[R] C)
    (h : Function.Surjective g) : Function.Surjective (pullbackFst f g) :=
  RingHom.surjective_pullbackFst_of_surjective (f : A →+* C) (g : B →+* C) h
/-
**AlgHom.surjective_pullbackSnd_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`
。
形式化陈述：surjective_pullbackSnd_of_surjective (f : A ->ₐ[R] C) (g : B ->ₐ[R] C) (h 
: Function.Surjective f) : Function.Surjective (pullbackSnd f g)
参数：f : A ->ₐ[R] C；g : B ->ₐ[R] C；h : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.surjective_pullbackSnd_of_surjective`：surjective_pullbackSnd_of_
surjective (f : R ->+* T) (g : S ->+* T) (h : Function.Surjective f) : Function.
Surjective (f.pullbackSnd g)
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
-/
theorem surjective_pullbackSnd_of_surjective (f : A →ₐ[R] C) (g : B →ₐ[R] C)
    (h : Function.Surjective f) : Function.Surjective (pullbackSnd f g) :=
  RingHom.surjective_pullbackSnd_of_surjective (f : A →+* C) (g : B →+* C) h
/-
**AlgHom.isLocalRing_pullback** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：isLocalRing_pullback [IsLocalRing A] (f : A ->ₐ[R] C) (g : B ->ₐ[R] C) [Is
LocalHom g] : IsLocalRing (f.pullback g)
参数：f : A ->ₐ[R] C；g : B ->ₐ[R] C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.isLocalRing_pullback`：isLocalRing_pullback [IsLocalRing R] (f : 
R ->+* T) (g : S ->+* T) [IsLocalHom g] : IsLocalRing (f.pullback g)
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `isLocalHom_toRingHom`：isLocalHom_toRingHom {F : Type*} [FunLike F R S] [
RingHomClass F R S] (f : F) [IsLocalHom f] : IsLocalHom (f : R ->+* S)
-/
theorem isLocalRing_pullback [IsLocalRing A] (f : A →ₐ[R] C) (g : B →ₐ[R] C)
    [IsLocalHom g] : IsLocalRing (f.pullback g) :=
  RingHom.isLocalRing_pullback (f : A →+* C) (g : B →+* C)

end Ring

end AlgHom

