/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau
-/
module

public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Algebra.Group.InjSurj
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Group.Basic

/-!
# Dependent functions with finite support

For a non-dependent version see `Mathlib/Data/Finsupp/Defs.lean`.

## Notation

This file introduces the notation `Π₀ a, β a` as notation for `DFinsupp β`, mirroring the `α →₀ β`
notation used for `Finsupp`. This works for nested binders too, with `Π₀ a b, γ a b` as notation
for `DFinsupp (fun a ↦ DFinsupp (γ a))`.

## Implementation notes

The support is internally represented (in the primed `DFinsupp.support'`) as a `Multiset` that
represents a superset of the true support of the function, quotiented by the always-true relation so
that this does not impact equality. This approach has computational benefits over storing a
`Finset`; it allows us to add together two finitely-supported functions without
having to evaluate the resulting function to recompute its support (which would required
decidability of `b = 0` for `b : β i`).

The true support of the function can still be recovered with `DFinsupp.support`; but these
decidability obligations are now postponed to when the support is actually needed. As a consequence,
there are two ways to sum a `DFinsupp`: with `DFinsupp.sum` which works over an arbitrary function
but requires recomputation of the support and therefore a `Decidable` argument; and with
`DFinsupp.sumAddHom` which requires an additive morphism, using its properties to show that
summing over a superset of the support is sufficient.

`Finsupp` takes an altogether different approach here; it uses `Classical.Decidable` and declares
the `Add` instance as noncomputable. This design difference is independent of the fact that
`DFinsupp` is dependently-typed and `Finsupp` is not; in future, we may want to align these two
definitions, or introduce two more definitions for the other combinations of decisions.
-/

@[expose] public section

assert_not_exists Finset.prod Submonoid

universe u u₁ u₂ v v₁ v₂ v₃ w x y l

variable {ι : Type u} {γ : Type w} {β : ι → Type v} {β₁ : ι → Type v₁} {β₂ : ι → Type v₂}

variable (β) in
/-- A dependent function `Π i, β i` with finite support, with notation `Π₀ i, β i`.

Note that `DFinsupp.support` is the preferred API for accessing the support of the function,
`DFinsupp.support'` is an implementation detail that aids computability; see the implementation
notes in this file for more information. -/
/-
**DFinsupp** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{ι : Type u} → (β : ι → Type v) → [(i : ι) → Zero (β i)] → Type (max u v)
参数：β : ι → Type v；i : ι；β i；max u v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A dependent function `Π i, β i` with finite support, with notation `Π₀ i, β i`.

Note that `DFinsupp.support` is the preferred API for accessing the support of t
he function,
`DFinsupp.support'` is an implementation detail that aids computability; see the
 implementation
notes in this file for more information.
-/
structure DFinsupp [∀ i, Zero (β i)] : Type max u v where mk' ::
  /-- The underlying function of a dependent function with finite support (aka `DFinsupp`). -/
  toFun : ∀ i, β i
  /-- The support of a dependent function with finite support (aka `DFinsupp`). -/
  support' : Trunc { s : Multiset ι // ∀ i, i ∈ s ∨ toFun i = 0 }

/-- `Π₀ i, β i` denotes the type of dependent functions with finite support `DFinsupp β`. -/
notation3 "Π₀ "(...)", "r:(scoped f => DFinsupp f) => r

namespace DFinsupp

section Basic

variable [∀ i, Zero (β i)] [∀ i, Zero (β₁ i)] [∀ i, Zero (β₂ i)]

/-
**DFinsupp.instDFunLike** 是 Mathlib 中的一个实例，位于命名空间 `DFinsupp`。
形式化陈述：instDFunLike : DFunLike (Π₀ i, β i) ι β
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDFunLike : DFunLike (Π₀ i, β i) ι β :=
  ⟨fun f => f.toFun, fun ⟨f₁, s₁⟩ ⟨f₂, s₁⟩ ↦ fun (h : f₁ = f₂) ↦ by
    subst h
    congr
    subsingleton ⟩

@[simp]
/-
**DFinsupp.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：toFun_eq_coe (f : Π₀ i, β i) : f.toFun = f
参数：f : Π₀ i, β i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFun_eq_coe (f : Π₀ i, β i) : f.toFun = f :=
  rfl

@[ext, grind ext]
/-
**DFinsupp.ext** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
参数：h : forall i, f i = g i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {f g : Π₀ i, β i} (h : ∀ i, f i = g i) : f = g :=
  DFunLike.ext _ _ h
/-
**DFinsupp.ne_iff** 是 Mathlib 中的一个引理，位于命名空间 `DFinsupp`。
形式化陈述：ne_iff {f g : Π₀ i, β i} : f != g ↔ exists i, f i != g i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ne_iff`：ne_iff {f g : F} : f != g ↔ exists a, f a != g a
-/
lemma ne_iff {f g : Π₀ i, β i} : f ≠ g ↔ ∃ i, f i ≠ g i := DFunLike.ne_iff
/-
**DFinsupp.** 是 Mathlib 中的一个实例，位于命名空间 `DFinsupp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero (Π₀ i, β i) :=
  ⟨⟨0, Trunc.mk <| ⟨∅, fun _ => Or.inr rfl⟩⟩⟩
/-
**DFinsupp.** 是 Mathlib 中的一个实例，位于命名空间 `DFinsupp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Π₀ i, β i) :=
  ⟨0⟩
/-
**DFinsupp.coe_mk'** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：∀ {ι : Type u} {β : ι → Type v} [inst : (i : ι) → Zero (β i)] (f : (i : ι)
 → β i)   (s : Trunc { s // ∀ (i : ι), i ∈ s ∨ f i = 0 }), ⇑{ toFun := f, suppor
t' := s } = f
参数：i : ι；β i；f : (i : ι) → β i；s : Trunc { s // ∀ (i : ι), i ∈ s ∨ f i = 0 }。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_mk' (f : ∀ i, β i) (s) : ⇑(⟨f, s⟩ : Π₀ i, β i) = f := rfl
/-
**DFinsupp.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：∀ {ι : Type u} {β : ι → Type v} [inst : (i : ι) → Zero (β i)], ⇑0 = 0
参数：i : ι；β i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_zero : ⇑(0 : Π₀ i, β i) = 0 := rfl
/-
**DFinsupp.zero_apply** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：zero_apply (i : ι) : (0 : Π₀ i, β i) i = 0
参数：i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_apply (i : ι) : (0 : Π₀ i, β i) i = 0 :=
  rfl

/-- The composition of `f : β₁ → β₂` and `g : Π₀ i, β₁ i` is
  `mapRange f hf g : Π₀ i, β₂ i`, well defined when `f 0 = 0`.

This preserves the structure on `f`, and exists in various bundled forms for when `f` is itself
bundled:

* `DFinsupp.mapRange.addMonoidHom`
* `DFinsupp.mapRange.addEquiv`
* `dfinsupp.mapRange.linearMap`
* `dfinsupp.mapRange.linearEquiv`
-/
/-
**DFinsupp.mapRange** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp`。
形式化陈述：mapRange (f : forall i, β₁ i -> β₂ i) (hf : forall i, f i 0 = 0) (x : Π₀ i
, β₁ i) : Π₀ i, β₂ i
参数：f : forall i, β₁ i -> β₂ i；hf : forall i, f i 0 = 0；x : Π₀ i, β₁ i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of `f : β₁ → β₂` and `g : Π₀ i, β₁ i` is
  `mapRange f hf g : Π₀ i, β₂ i`, well defined when `f 0 = 0`.

This preserves the structure on `f`, and exists in various bundled forms for whe
n `f` is itself
bundled:

* `DFinsupp.mapRange.addMonoidHom`
* `DFinsupp.mapRange.addEquiv`
* `dfinsupp.mapRange.linearMap`
* `dfinsupp.mapRange.linearEquiv`
-/
def mapRange (f : ∀ i, β₁ i → β₂ i) (hf : ∀ i, f i 0 = 0) (x : Π₀ i, β₁ i) : Π₀ i, β₂ i :=
  ⟨fun i => f i (x i),
    x.support'.map fun s => ⟨s.1, fun i => (s.2 i).imp_right fun h : x i = 0 => by
      rw [← hf i, ← h]⟩⟩

@[simp]
/-
**DFinsupp.mapRange_apply** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：mapRange_apply (f : forall i, β₁ i -> β₂ i) (hf : forall i, f i 0 = 0) (g 
: Π₀ i, β₁ i) (i : ι) : mapRange f hf g i = f i (g i)
参数：f : forall i, β₁ i -> β₂ i；hf : forall i, f i 0 = 0；g : Π₀ i, β₁ i；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapRange_apply (f : ∀ i, β₁ i → β₂ i) (hf : ∀ i, f i 0 = 0) (g : Π₀ i, β₁ i) (i : ι) :
    mapRange f hf g i = f i (g i) :=
  rfl

@[simp]
/-
**DFinsupp.mapRange_id** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：mapRange_id (h : forall i, id (0 : β₁ i) = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
-/
theorem mapRange_id (h : ∀ i, id (0 : β₁ i) = 0 := fun _ => rfl) (g : Π₀ i : ι, β₁ i) :
    mapRange (fun i => (id : β₁ i → β₁ i)) h g = g := by
  ext
  rfl
/-
**DFinsupp.mapRange_comp** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：mapRange_comp (f : forall i, β₁ i -> β₂ i) (f₂ : forall i, β i -> β₁ i) (h
f : forall i, f i 0 = 0) (hf₂ : forall i, f₂ i 0 = 0) (h : forall i, (f i ∘ f₂ i
) 0 = 0) (g : Π₀ i : ι, β i) : mapRange (fun i => f i ∘ f₂ i) h g = mapRange f h
f (mapRange f₂ hf₂ g)
参数：f : forall i, β₁ i -> β₂ i；f₂ : forall i, β i -> β₁ i；hf : forall i, f i 0 = 
0；hf₂ : forall i, f₂ i 0 = 0；h : forall i, (f i ∘ f₂ i) 0 = 0；g : Π₀ i : ι, β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
-/
theorem mapRange_comp (f : ∀ i, β₁ i → β₂ i) (f₂ : ∀ i, β i → β₁ i) (hf : ∀ i, f i 0 = 0)
    (hf₂ : ∀ i, f₂ i 0 = 0) (h : ∀ i, (f i ∘ f₂ i) 0 = 0) (g : Π₀ i : ι, β i) :
    mapRange (fun i => f i ∘ f₂ i) h g = mapRange f hf (mapRange f₂ hf₂ g) := by
  ext
  simp only [mapRange_apply]; rfl

@[simp]
/-
**DFinsupp.mapRange_zero** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：mapRange_zero (f : forall i, β₁ i -> β₂ i) (hf : forall i, f i 0 = 0) : ma
pRange f hf (0 : Π₀ i, β₁ i) = 0
参数：f : forall i, β₁ i -> β₂ i；hf : forall i, f i 0 = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mapRange_zero (f : ∀ i, β₁ i → β₂ i) (hf : ∀ i, f i 0 = 0) :
    mapRange f hf (0 : Π₀ i, β₁ i) = 0 := by
  ext
  simp only [mapRange_apply, coe_zero, Pi.zero_apply, hf]

/-- Let `f i` be a binary operation `β₁ i → β₂ i → β i` such that `f i 0 0 = 0`.
Then `zipWith f hf` is a binary operation `Π₀ i, β₁ i → Π₀ i, β₂ i → Π₀ i, β i`. -/
/-
**DFinsupp.zipWith** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp`。
形式化陈述：zipWith (f : forall i, β₁ i -> β₂ i -> β i) (hf : forall i, f i 0 0 = 0) (
x : Π₀ i, β₁ i) (y : Π₀ i, β₂ i) : Π₀ i, β i
参数：f : forall i, β₁ i -> β₂ i -> β i；hf : forall i, f i 0 0 = 0；x : Π₀ i, β₁ i；y
 : Π₀ i, β₂ i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `f i` be a binary operation `β₁ i → β₂ i → β i` such that `f i 0 0 = 0`.
Then `zipWith f hf` is a binary operation `Π₀ i, β₁ i → Π₀ i, β₂ i → Π₀ i, β i`.
-/
def zipWith (f : ∀ i, β₁ i → β₂ i → β i) (hf : ∀ i, f i 0 0 = 0) (x : Π₀ i, β₁ i) (y : Π₀ i, β₂ i) :
    Π₀ i, β i :=
  ⟨fun i => f i (x i) (y i), by
    refine x.support'.bind fun xs => ?_
    refine y.support'.map fun ys => ?_
    refine ⟨xs + ys, fun i => ?_⟩
    obtain h1 | (h1 : x i = 0) := xs.prop i
    · grind
    obtain h2 | (h2 : y i = 0) := ys.prop i
    · grind
    grind⟩

@[simp, grind =]
/-
**DFinsupp.zipWith_apply** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：zipWith_apply (f : forall i, β₁ i -> β₂ i -> β i) (hf : forall i, f i 0 0 
= 0) (g₁ : Π₀ i, β₁ i) (g₂ : Π₀ i, β₂ i) (i : ι) : zipWith f hf g₁ g₂ i = f i (g
₁ i) (g₂ i)
参数：f : forall i, β₁ i -> β₂ i -> β i；hf : forall i, f i 0 0 = 0；g₁ : Π₀ i, β₁ i；
g₂ : Π₀ i, β₂ i；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zipWith_apply (f : ∀ i, β₁ i → β₂ i → β i) (hf : ∀ i, f i 0 0 = 0) (g₁ : Π₀ i, β₁ i)
    (g₂ : Π₀ i, β₂ i) (i : ι) : zipWith f hf g₁ g₂ i = f i (g₁ i) (g₂ i) :=
  rfl

section Piecewise

variable (x y : Π₀ i, β i) (s : Set ι) [∀ i, Decidable (i ∈ s)]

/-- `x.piecewise y s` is the finitely supported function equal to `x` on the set `s`,
  and to `y` on its complement. -/
/-
**DFinsupp.piecewise** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp`。
形式化陈述：piecewise : Π₀ i, β i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`x.piecewise y s` is the finitely supported function equal to `x` on the set `s`
,
  and to `y` on its complement.
-/
def piecewise : Π₀ i, β i :=
  zipWith (fun i x y => if i ∈ s then x else y) (fun _ => ite_self 0) x y
/-
**DFinsupp.piecewise_apply** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：piecewise_apply (i : ι) : x.piecewise y s i = if i in s then x i else y i
参数：i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem piecewise_apply (i : ι) : x.piecewise y s i = if i ∈ s then x i else y i :=
  rfl

@[simp, norm_cast]
/-
**DFinsupp.coe_piecewise** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：coe_piecewise : ⇑(x.piecewise y s) = s.piecewise x y
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_piecewise : ⇑(x.piecewise y s) = s.piecewise x y :=
  rfl

end Piecewise

end Basic

section Algebra

/-
**DFinsupp.** 是 Mathlib 中的一个实例，位于命名空间 `DFinsupp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, AddZeroClass (β i)] : Add (Π₀ i, β i) :=
  ⟨zipWith (fun _ => (· + ·)) fun _ => add_zero 0⟩
/-
**DFinsupp.add_apply** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：add_apply [forall i, AddZeroClass (β i)] (g₁ g₂ : Π₀ i, β i) (i : ι) : (g₁
 + g₂) i = g₁ i + g₂ i
参数：β i；g₁ g₂ : Π₀ i, β i；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_apply [∀ i, AddZeroClass (β i)] (g₁ g₂ : Π₀ i, β i) (i : ι) :
    (g₁ + g₂) i = g₁ i + g₂ i :=
  rfl

@[simp, norm_cast]
/-
**DFinsupp.coe_add** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：coe_add [forall i, AddZeroClass (β i)] (g₁ g₂ : Π₀ i, β i) : ⇑(g₁ + g₂) = 
g₁ + g₂
参数：β i；g₁ g₂ : Π₀ i, β i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_add [∀ i, AddZeroClass (β i)] (g₁ g₂ : Π₀ i, β i) : ⇑(g₁ + g₂) = g₁ + g₂ :=
  rfl
/-
**DFinsupp.addZeroClass** 是 Mathlib 中的一个实例，位于命名空间 `DFinsupp`。
形式化陈述：addZeroClass [forall i, AddZeroClass (β i)] : AddZeroClass (Π₀ i, β i)
参数：β i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.coe_add`：coe_add [forall i, AddZeroClass (β i)] (g₁ g₂ : Π₀ i, 
β i) : ⇑(g₁ + g₂) = g₁ + g₂
-/
instance addZeroClass [∀ i, AddZeroClass (β i)] : AddZeroClass (Π₀ i, β i) :=
  DFunLike.coe_injective.addZeroClass _ coe_zero coe_add
/-
**DFinsupp.instIsLeftCancelAdd** 是 Mathlib 中的一个实例，位于命名空间 `DFinsupp`。
形式化陈述：instIsLeftCancelAdd [forall i, AddZeroClass (β i)] [forall i, IsLeftCancel
Add (β i)] : IsLeftCancelAdd (Π₀ i, β i) where add_left_cancel _ _ _ h
参数：β i；β i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `add_left_cancel`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G] {a 
b c : G}, a + b = a + c → b = c
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
instance instIsLeftCancelAdd [∀ i, AddZeroClass (β i)] [∀ i, IsLeftCancelAdd (β i)] :
    IsLeftCancelAdd (Π₀ i, β i) where
  add_left_cancel _ _ _ h := ext fun x => add_left_cancel <| DFunLike.congr_fun h x
/-
**DFinsupp.instIsRightCancelAdd** 是 Mathlib 中的一个实例，位于命名空间 `DFinsupp`。
形式化陈述：instIsRightCancelAdd [forall i, AddZeroClass (β i)] [forall i, IsRightCanc
elAdd (β i)] : IsRightCancelAdd (Π₀ i, β i) where add_right_cancel _ _ _ h
参数：β i；β i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `add_right_cancel`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd G] {
a b c : G}, a + b = c + b → a = c
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
instance instIsRightCancelAdd [∀ i, AddZeroClass (β i)] [∀ i, IsRightCancelAdd (β i)] :
    IsRightCancelAdd (Π₀ i, β i) where
  add_right_cancel _ _ _ h := ext fun x => add_right_cancel <| DFunLike.congr_fun h x
/-
**DFinsupp.instIsCancelAdd** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：∀ {ι : Type u} {β : ι → Type v} [inst : (i : ι) → AddZeroClass (β i)] [∀ (
i : ι), IsCancelAdd (β i)],   IsCancelAdd (Π₀ (i : ι), β i)
参数：i : ι；β i；i : ι；β i；Π₀ (i : ι), β i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCancelAdd.toIsLeftCancelAdd`：∀ {G : Type u} {inst : Add G} [self : IsC
ancelAdd G], IsLeftCancelAdd G
· 使用定理 `IsCancelAdd.toIsRightCancelAdd`：∀ {G : Type u} {inst : Add G} [self : Is
CancelAdd G], IsRightCancelAdd G
-/
instance instIsCancelAdd [∀ i, AddZeroClass (β i)] [∀ i, IsCancelAdd (β i)] :
    IsCancelAdd (Π₀ i, β i) where

/-- Note the general `SMul` instance doesn't apply as `ℕ` is not distributive
unless `β i`'s addition is commutative. -/
/-
**DFinsupp.hasNatScalar** 是 Mathlib 中的一个实例，位于命名空间 `DFinsupp`。
形式化陈述：hasNatScalar [forall i, AddMonoid (β i)] : SMul Nat (Π₀ i, β i)
参数：β i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Note the general `SMul` instance doesn't apply as `ℕ` is not distributive
unless `β i`'s addition is commutative.
-/
instance hasNatScalar [∀ i, AddMonoid (β i)] : SMul ℕ (Π₀ i, β i) :=
  ⟨fun c v => v.mapRange (fun _ => (c • ·)) fun _ => nsmul_zero _⟩
/-
**DFinsupp.nsmul_apply** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：nsmul_apply [forall i, AddMonoid (β i)] (b : Nat) (v : Π₀ i, β i) (i : ι) 
: (b • v) i = b • v i
参数：β i；b : Nat；v : Π₀ i, β i；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nsmul_apply [∀ i, AddMonoid (β i)] (b : ℕ) (v : Π₀ i, β i) (i : ι) : (b • v) i = b • v i :=
  rfl

@[simp, norm_cast]
/-
**DFinsupp.coe_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：coe_nsmul [forall i, AddMonoid (β i)] (b : Nat) (v : Π₀ i, β i) : ⇑(b • v)
 = b • ⇑v
参数：β i；b : Nat；v : Π₀ i, β i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_nsmul [∀ i, AddMonoid (β i)] (b : ℕ) (v : Π₀ i, β i) : ⇑(b • v) = b • ⇑v :=
  rfl
/-
**DFinsupp.** 是 Mathlib 中的一个实例，位于命名空间 `DFinsupp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, AddMonoid (β i)] : AddMonoid (Π₀ i, β i) :=
  DFunLike.coe_injective.addMonoid _ coe_zero coe_add fun _ _ => coe_nsmul _ _

/-- Coercion from a `DFinsupp` to a pi type is an `AddMonoidHom`. -/
/-
**DFinsupp.coeFnAddMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp`。
形式化陈述：coeFnAddMonoidHom [forall i, AddZeroClass (β i)] : (Π₀ i, β i) ->+ forall 
i, β i where toFun
参数：β i。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.coe_add`：coe_add [forall i, AddZeroClass (β i)] (g₁ g₂ : Π₀ i, 
β i) : ⇑(g₁ + g₂) = g₁ + g₂

--- 原说明 ---
Coercion from a `DFinsupp` to a pi type is an `AddMonoidHom`.
-/
def coeFnAddMonoidHom [∀ i, AddZeroClass (β i)] : (Π₀ i, β i) →+ ∀ i, β i where
  toFun := (⇑)
  map_zero' := coe_zero
  map_add' := coe_add

@[simp]
/-
**DFinsupp.coeFnAddMonoidHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `DFinsupp`。
形式化陈述：coeFnAddMonoidHom_apply [forall i, AddZeroClass (β i)] (v : Π₀ i, β i) : c
oeFnAddMonoidHom v = v
参数：β i；v : Π₀ i, β i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coeFnAddMonoidHom_apply [∀ i, AddZeroClass (β i)] (v : Π₀ i, β i) : coeFnAddMonoidHom v = v :=
  rfl
/-
**DFinsupp.addCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `DFinsupp`。
形式化陈述：addCommMonoid [forall i, AddCommMonoid (β i)] : AddCommMonoid (Π₀ i, β i)
参数：β i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addCommMonoid [∀ i, AddCommMonoid (β i)] : AddCommMonoid (Π₀ i, β i) :=
  fast_instance% DFunLike.coe_injective.addCommMonoid _ coe_zero coe_add fun _ _ => coe_nsmul _ _
/-
**DFinsupp.** 是 Mathlib 中的一个实例，位于命名空间 `DFinsupp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, AddGroup (β i)] : Neg (Π₀ i, β i) :=
  ⟨fun f => f.mapRange (fun _ => Neg.neg) fun _ => neg_zero⟩
/-
**DFinsupp.neg_apply** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：neg_apply [forall i, AddGroup (β i)] (g : Π₀ i, β i) (i : ι) : (-g) i = -g
 i
参数：β i；g : Π₀ i, β i；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neg_apply [∀ i, AddGroup (β i)] (g : Π₀ i, β i) (i : ι) : (-g) i = -g i :=
  rfl
/-
**DFinsupp.coe_neg** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：∀ {ι : Type u} {β : ι → Type v} [inst : (i : ι) → AddGroup (β i)] (g : Π₀ 
(i : ι), β i), ⇑(-g) = -⇑g
参数：i : ι；β i；g : Π₀ (i : ι), β i；-g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_neg [∀ i, AddGroup (β i)] (g : Π₀ i, β i) : ⇑(-g) = -g := rfl
/-
**DFinsupp.** 是 Mathlib 中的一个实例，位于命名空间 `DFinsupp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, AddGroup (β i)] : Sub (Π₀ i, β i) :=
  ⟨zipWith (fun _ => Sub.sub) fun _ => sub_zero 0⟩
/-
**DFinsupp.sub_apply** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：sub_apply [forall i, AddGroup (β i)] (g₁ g₂ : Π₀ i, β i) (i : ι) : (g₁ - g
₂) i = g₁ i - g₂ i
参数：β i；g₁ g₂ : Π₀ i, β i；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sub_apply [∀ i, AddGroup (β i)] (g₁ g₂ : Π₀ i, β i) (i : ι) : (g₁ - g₂) i = g₁ i - g₂ i :=
  rfl

@[simp, norm_cast]
/-
**DFinsupp.coe_sub** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：coe_sub [forall i, AddGroup (β i)] (g₁ g₂ : Π₀ i, β i) : ⇑(g₁ - g₂) = g₁ -
 g₂
参数：β i；g₁ g₂ : Π₀ i, β i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sub [∀ i, AddGroup (β i)] (g₁ g₂ : Π₀ i, β i) : ⇑(g₁ - g₂) = g₁ - g₂ :=
  rfl

/-- Note the general `SMul` instance doesn't apply as `ℤ` is not distributive
unless `β i`'s addition is commutative. -/
/-
**DFinsupp.hasIntScalar** 是 Mathlib 中的一个实例，位于命名空间 `DFinsupp`。
形式化陈述：hasIntScalar [forall i, AddGroup (β i)] : SMul Int (Π₀ i, β i)
参数：β i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Note the general `SMul` instance doesn't apply as `ℤ` is not distributive
unless `β i`'s addition is commutative.
-/
instance hasIntScalar [∀ i, AddGroup (β i)] : SMul ℤ (Π₀ i, β i) :=
  ⟨fun c v => v.mapRange (fun _ => (c • ·)) fun _ => zsmul_zero _⟩
/-
**DFinsupp.zsmul_apply** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：zsmul_apply [forall i, AddGroup (β i)] (b : Int) (v : Π₀ i, β i) (i : ι) :
 (b • v) i = b • v i
参数：β i；b : Int；v : Π₀ i, β i；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zsmul_apply [∀ i, AddGroup (β i)] (b : ℤ) (v : Π₀ i, β i) (i : ι) : (b • v) i = b • v i :=
  rfl

@[simp, norm_cast]
/-
**DFinsupp.coe_zsmul** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：coe_zsmul [forall i, AddGroup (β i)] (b : Int) (v : Π₀ i, β i) : ⇑(b • v) 
= b • ⇑v
参数：β i；b : Int；v : Π₀ i, β i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_zsmul [∀ i, AddGroup (β i)] (b : ℤ) (v : Π₀ i, β i) : ⇑(b • v) = b • ⇑v :=
  rfl
/-
**DFinsupp.** 是 Mathlib 中的一个实例，位于命名空间 `DFinsupp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, AddGroup (β i)] : AddGroup (Π₀ i, β i) :=
  fast_instance% DFunLike.coe_injective.addGroup _ coe_zero coe_add coe_neg coe_sub
    (fun _ _ => coe_nsmul _ _) fun _ _ => coe_zsmul _ _
/-
**DFinsupp.addCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `DFinsupp`。
形式化陈述：addCommGroup [forall i, AddCommGroup (β i)] : AddCommGroup (Π₀ i, β i)
参数：β i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addCommGroup [∀ i, AddCommGroup (β i)] : AddCommGroup (Π₀ i, β i) :=
  fast_instance% DFunLike.coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub
    (fun _ _ => coe_nsmul _ _) fun _ _ => coe_zsmul _ _

end Algebra

section FilterAndSubtypeDomain

/-- `Filter p f` is the function which is `f i` if `p i` is true and 0 otherwise. -/
/-
**DFinsupp.filter** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp`。
形式化陈述：filter [forall i, Zero (β i)] (p : ι -> Prop) [DecidablePred p] (x : Π₀ i,
 β i) : Π₀ i, β i
参数：β i；p : ι -> Prop；x : Π₀ i, β i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Filter p f` is the function which is `f i` if `p i` is true and 0 otherwise.
-/
def filter [∀ i, Zero (β i)] (p : ι → Prop) [DecidablePred p] (x : Π₀ i, β i) : Π₀ i, β i :=
  ⟨fun i => if p i then x i else 0,
    x.support'.map fun xs =>
      ⟨xs.1, fun i => (xs.prop i).imp_right fun H : x i = 0 => by simp only [H, ite_self]⟩⟩

@[simp, grind =]
/-
**DFinsupp.filter_apply** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：filter_apply [forall i, Zero (β i)] (p : ι -> Prop) [DecidablePred p] (i :
 ι) (f : Π₀ i, β i) : f.filter p i = if p i then f i else 0
参数：β i；p : ι -> Prop；i : ι；f : Π₀ i, β i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem filter_apply [∀ i, Zero (β i)] (p : ι → Prop) [DecidablePred p] (i : ι) (f : Π₀ i, β i) :
    f.filter p i = if p i then f i else 0 :=
  rfl
/-
**DFinsupp.filter_apply_pos** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：filter_apply_pos [forall i, Zero (β i)] {p : ι -> Prop} [DecidablePred p] 
(f : Π₀ i, β i) {i : ι} (h : p i) : f.filter p i = f i
参数：β i；f : Π₀ i, β i；h : p i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem filter_apply_pos [∀ i, Zero (β i)] {p : ι → Prop} [DecidablePred p] (f : Π₀ i, β i) {i : ι}
    (h : p i) : f.filter p i = f i := by grind
/-
**DFinsupp.filter_apply_neg** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：filter_apply_neg [forall i, Zero (β i)] {p : ι -> Prop} [DecidablePred p] 
(f : Π₀ i, β i) {i : ι} (h : ¬p i) : f.filter p i = 0
参数：β i；f : Π₀ i, β i；h : ¬p i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem filter_apply_neg [∀ i, Zero (β i)] {p : ι → Prop} [DecidablePred p] (f : Π₀ i, β i) {i : ι}
    (h : ¬p i) : f.filter p i = 0 := by grind
/-
**DFinsupp.filter_add_filter_not** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：∀ {ι : Type u} {β : ι → Type v} [inst : (i : ι) → AddZeroClass (β i)] (f :
 Π₀ (i : ι), β i) (p : ι → Prop)   [inst_1 : DecidablePred p], DFinsupp.filter p
 f + DFinsupp.filter (fun i => ¬p i) f = f
参数：i : ι；β i；f : Π₀ (i : ι), β i；p : ι → Prop；fun i => ¬p i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `not_not_intro`：∀ {p : Prop}, p → ¬¬p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
@[simp] theorem filter_add_filter_not [∀ i, AddZeroClass (β i)] (f : Π₀ i, β i) (p : ι → Prop)
    [DecidablePred p] : (f.filter p + f.filter fun i => ¬p i) = f :=
  ext fun i => by
    simp only [add_apply, filter_apply]; split_ifs <;> simp only [add_zero, zero_add]

@[deprecated (since := "2026-05-04")] alias filter_pos_add_filter_neg := filter_add_filter_not

@[simp]
/-
**DFinsupp.filter_zero** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：filter_zero [forall i, Zero (β i)] (p : ι -> Prop) [DecidablePred p] : (0 
: Π₀ i, β i).filter p = 0
参数：β i；p : ι -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem filter_zero [∀ i, Zero (β i)] (p : ι → Prop) [DecidablePred p] :
    (0 : Π₀ i, β i).filter p = 0 := by
  ext
  simp

@[simp]
/-
**DFinsupp.filter_add** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：filter_add [forall i, AddZeroClass (β i)] (p : ι -> Prop) [DecidablePred p
] (f g : Π₀ i, β i) : (f + g).filter p = f.filter p + g.filter p
参数：β i；p : ι -> Prop；f g : Π₀ i, β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_add_zero`：∀ {M : Type u_4} [inst : AddZeroClass M] {P : Prop} [inst_
1 : Decidable P] {a b : M},   (if P then a + b else 0) = (if P then a else 0) + 
if…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem filter_add [∀ i, AddZeroClass (β i)] (p : ι → Prop) [DecidablePred p] (f g : Π₀ i, β i) :
    (f + g).filter p = f.filter p + g.filter p := by
  ext
  simp [ite_add_zero]

variable (γ β)

/-- `DFinsupp.filter` as an `AddMonoidHom`. -/
@[simps]
/-
**DFinsupp.filterAddMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp`。
形式化陈述：filterAddMonoidHom [forall i, AddZeroClass (β i)] (p : ι -> Prop) [Decidab
lePred p] : (Π₀ i, β i) ->+ Π₀ i, β i where toFun
参数：β i；p : ι -> Prop。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.filter_add`：filter_add [forall i, AddZeroClass (β i)] (p : ι ->
 Prop) [DecidablePred p] (f g : Π₀ i, β i) : (f + g).filter p = f.filter p + g.f
ilter p

--- 原说明 ---
`DFinsupp.filter` as an `AddMonoidHom`.
-/
def filterAddMonoidHom [∀ i, AddZeroClass (β i)] (p : ι → Prop) [DecidablePred p] :
    (Π₀ i, β i) →+ Π₀ i, β i where
  toFun := filter p
  map_zero' := filter_zero p
  map_add' := filter_add p

variable {γ β}

@[simp]
/-
**DFinsupp.filter_neg** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：filter_neg [forall i, AddGroup (β i)] (p : ι -> Prop) [DecidablePred p] (f
 : Π₀ i, β i) : (-f).filter p = -f.filter p
参数：β i；p : ι -> Prop；f : Π₀ i, β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.map_neg`：∀ {α : Type u_2} {β : Type u_3} [inst : AddGroup α
] [inst_1 : SubtractionMonoid β] (f : α →+ β) (a : α), f (-a) = -f a
-/
theorem filter_neg [∀ i, AddGroup (β i)] (p : ι → Prop) [DecidablePred p] (f : Π₀ i, β i) :
    (-f).filter p = -f.filter p :=
  (filterAddMonoidHom β p).map_neg f

@[simp]
/-
**DFinsupp.filter_sub** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：filter_sub [forall i, AddGroup (β i)] (p : ι -> Prop) [DecidablePred p] (f
 g : Π₀ i, β i) : (f - g).filter p = f.filter p - g.filter p
参数：β i；p : ι -> Prop；f g : Π₀ i, β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.map_sub`：∀ {α : Type u_2} {β : Type u_3} [inst : AddGroup α
] [inst_1 : SubtractionMonoid β] (f : α →+ β) (g h : α),   f (g - h) = f g - f h
-/
theorem filter_sub [∀ i, AddGroup (β i)] (p : ι → Prop) [DecidablePred p] (f g : Π₀ i, β i) :
    (f - g).filter p = f.filter p - g.filter p :=
  (filterAddMonoidHom β p).map_sub f g

/-- `subtypeDomain p f` is the restriction of the finitely supported function
  `f` to the subtype `p`. -/
/-
**DFinsupp.subtypeDomain** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp`。
形式化陈述：subtypeDomain [forall i, Zero (β i)] (p : ι -> Prop) [DecidablePred p] (x 
: Π₀ i, β i) : Π₀ i : Subtype p, β i
参数：β i；p : ι -> Prop；x : Π₀ i, β i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`subtypeDomain p f` is the restriction of the finitely supported function
  `f` to the subtype `p`.
-/
def subtypeDomain [∀ i, Zero (β i)] (p : ι → Prop) [DecidablePred p] (x : Π₀ i, β i) :
    Π₀ i : Subtype p, β i :=
  ⟨fun i => x (i : ι),
    x.support'.map fun xs =>
      ⟨(Multiset.filter p xs.1).attach.map fun j => ⟨j.1, (Multiset.mem_filter.1 j.2).2⟩, fun i =>
        (xs.prop i).imp_left fun H =>
          Multiset.mem_map.2
            ⟨⟨i, Multiset.mem_filter.2 ⟨H, i.2⟩⟩, Multiset.mem_attach _ _, Subtype.eta _ _⟩⟩⟩

@[simp]
/-
**DFinsupp.subtypeDomain_zero** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：subtypeDomain_zero [forall i, Zero (β i)] {p : ι -> Prop} [DecidablePred p
] : subtypeDomain p (0 : Π₀ i, β i) = 0
参数：β i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subtypeDomain_zero [∀ i, Zero (β i)] {p : ι → Prop} [DecidablePred p] :
    subtypeDomain p (0 : Π₀ i, β i) = 0 :=
  rfl

@[simp]
/-
**DFinsupp.subtypeDomain_apply** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：subtypeDomain_apply [forall i, Zero (β i)] {p : ι -> Prop} [DecidablePred 
p] {i : Subtype p} {v : Π₀ i, β i} : (subtypeDomain p v) i = v i
参数：β i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subtypeDomain_apply [∀ i, Zero (β i)] {p : ι → Prop} [DecidablePred p] {i : Subtype p}
    {v : Π₀ i, β i} : (subtypeDomain p v) i = v i :=
  rfl

@[simp]
/-
**DFinsupp.subtypeDomain_add** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：subtypeDomain_add [forall i, AddZeroClass (β i)] {p : ι -> Prop} [Decidabl
ePred p] (v v' : Π₀ i, β i) : (v + v').subtypeDomain p = v.subtypeDomain p + v'.
subtypeDomain p
参数：β i；v v' : Π₀ i, β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
theorem subtypeDomain_add [∀ i, AddZeroClass (β i)] {p : ι → Prop} [DecidablePred p]
    (v v' : Π₀ i, β i) : (v + v').subtypeDomain p = v.subtypeDomain p + v'.subtypeDomain p :=
  DFunLike.coe_injective rfl

variable (γ β)

/-- `subtypeDomain` but as an `AddMonoidHom`. -/
@[simps]
/-
**DFinsupp.subtypeDomainAddMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp`。
形式化陈述：subtypeDomainAddMonoidHom [forall i, AddZeroClass (β i)] (p : ι -> Prop) [
DecidablePred p] : (Π₀ i : ι, β i) ->+ Π₀ i : Subtype p, β i where toFun
参数：β i；p : ι -> Prop。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.subtypeDomain_add`：subtypeDomain_add [forall i, AddZeroClass (β
 i)] {p : ι -> Prop} [DecidablePred p] (v v' : Π₀ i, β i) : (v + v').subtypeDoma
in p = v.subtype…

--- 原说明 ---
`subtypeDomain` but as an `AddMonoidHom`.
-/
def subtypeDomainAddMonoidHom [∀ i, AddZeroClass (β i)] (p : ι → Prop) [DecidablePred p] :
    (Π₀ i : ι, β i) →+ Π₀ i : Subtype p, β i where
  toFun := subtypeDomain p
  map_zero' := subtypeDomain_zero
  map_add' := subtypeDomain_add

variable {γ β}

@[simp]
/-
**DFinsupp.subtypeDomain_neg** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：subtypeDomain_neg [forall i, AddGroup (β i)] {p : ι -> Prop} [DecidablePre
d p] {v : Π₀ i, β i} : (-v).subtypeDomain p = -v.subtypeDomain p
参数：β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
theorem subtypeDomain_neg [∀ i, AddGroup (β i)] {p : ι → Prop} [DecidablePred p] {v : Π₀ i, β i} :
    (-v).subtypeDomain p = -v.subtypeDomain p :=
  DFunLike.coe_injective rfl

@[simp]
/-
**DFinsupp.subtypeDomain_sub** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：subtypeDomain_sub [forall i, AddGroup (β i)] {p : ι -> Prop} [DecidablePre
d p] {v v' : Π₀ i, β i} : (v - v').subtypeDomain p = v.subtypeDomain p - v'.subt
ypeDomain p
参数：β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
theorem subtypeDomain_sub [∀ i, AddGroup (β i)] {p : ι → Prop} [DecidablePred p]
    {v v' : Π₀ i, β i} : (v - v').subtypeDomain p = v.subtypeDomain p - v'.subtypeDomain p :=
  DFunLike.coe_injective rfl

end FilterAndSubtypeDomain

section Basic

variable [∀ i, Zero (β i)]

/-
**DFinsupp.finite_support** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：finite_support (f : Π₀ i, β i) : Set.Finite { i | f i != 0 }
参数：f : Π₀ i, β i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Trunc.induction_on`：∀ {α : Sort u_1} {β : Trunc α → Prop} (q : Trunc α),
 (∀ (a : α), β (Trunc.mk a)) → β q
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Multiset.finite_toSet`：finite_toSet (s : Multiset α) : { x | x in s }.Fi
nite
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem finite_support (f : Π₀ i, β i) : Set.Finite { i | f i ≠ 0 } :=
  Trunc.induction_on f.support' fun xs ↦
    xs.1.finite_toSet.subset fun i H ↦ ((xs.prop i).resolve_right H)

section DecidableEq
variable [DecidableEq ι]

/-- Create an element of `Π₀ i, β i` from a finset `s` and a function `x`
defined on this `Finset`. -/
/-
**DFinsupp.mk** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp`。
形式化陈述：mk (s : Finset ι) (x : forall i : (↑s : Set ι), β (i : ι)) : Π₀ i, β i
参数：s : Finset ι；x : forall i : (↑s : Set ι), β (i : ι)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Create an element of `Π₀ i, β i` from a finset `s` and a function `x`
defined on this `Finset`.
-/
def mk (s : Finset ι) (x : ∀ i : (↑s : Set ι), β (i : ι)) : Π₀ i, β i :=
  ⟨fun i => if H : i ∈ s then x ⟨i, H⟩ else 0,
    Trunc.mk ⟨s.1, fun i => if H : i ∈ s then Or.inl H else Or.inr <| dif_neg H⟩⟩

variable {s : Finset ι} {x : ∀ i : (↑s : Set ι), β i} {i : ι}

@[simp, grind =]
/-
**DFinsupp.mk_apply** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：mk_apply : (mk s x : forall i, β i) i = if H : i in s then x ⟨i, H⟩ else 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_apply : (mk s x : ∀ i, β i) i = if H : i ∈ s then x ⟨i, H⟩ else 0 :=
  rfl
/-
**DFinsupp.mk_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：mk_of_mem (hi : i in s) : (mk s x : forall i, β i) i = x ⟨i, hi⟩
参数：hi : i in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem mk_of_mem (hi : i ∈ s) : (mk s x : ∀ i, β i) i = x ⟨i, hi⟩ :=
  dif_pos hi
/-
**DFinsupp.mk_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：mk_of_notMem (hi : i ∉ s) : (mk s x : forall i, β i) i = 0
参数：hi : i ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem mk_of_notMem (hi : i ∉ s) : (mk s x : ∀ i, β i) i = 0 :=
  dif_neg hi
/-
**DFinsupp.mk_injective** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：mk_injective (s : Finset ι) : Function.Injective (@mk ι β _ _ s)
参数：s : Finset ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem mk_injective (s : Finset ι) : Function.Injective (@mk ι β _ _ s) := by
  intro x y H
  ext i
  have h1 : (mk s x : ∀ i, β i) i = (mk s y : ∀ i, β i) i := by grind
  grind

end DecidableEq

/-
**DFinsupp.unique** 是 Mathlib 中的一个实例，位于命名空间 `DFinsupp`。
形式化陈述：unique [forall i, Subsingleton (β i)] : Unique (Π₀ i, β i)
参数：β i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
-/
instance unique [∀ i, Subsingleton (β i)] : Unique (Π₀ i, β i) :=
  DFunLike.coe_injective.unique
/-
**DFinsupp.uniqueOfIsEmpty** 是 Mathlib 中的一个实例，位于命名空间 `DFinsupp`。
形式化陈述：uniqueOfIsEmpty [IsEmpty ι] : Unique (Π₀ i, β i)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance uniqueOfIsEmpty [IsEmpty ι] : Unique (Π₀ i, β i) :=
  DFunLike.coe_injective.unique

/-- Given `Fintype ι`, `equivFunOnFintype` is the `Equiv` between `Π₀ i, β i` and `Π i, β i`.
  (All dependent functions on a finite type are finitely supported.) -/
@[simps apply]
/-
**DFinsupp.equivFunOnFintype** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp`。
形式化陈述：equivFunOnFintype [Fintype ι] : (Π₀ i, β i) ≃ forall i, β i where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `Fintype ι`, `equivFunOnFintype` is the `Equiv` between `Π₀ i, β i` and `Π
 i, β i`.
  (All dependent functions on a finite type are finitely supported.)
-/
def equivFunOnFintype [Fintype ι] : (Π₀ i, β i) ≃ ∀ i, β i where
  toFun := (⇑)
  invFun f := ⟨f, Trunc.mk ⟨Finset.univ.1, fun _ => Or.inl <| Finset.mem_univ_val _⟩⟩
  left_inv _ := DFunLike.coe_injective rfl

@[simp]
/-
**DFinsupp.equivFunOnFintype_symm_coe** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：equivFunOnFintype_symm_coe [Fintype ι] (f : Π₀ i, β i) : equivFunOnFintype
.symm f = f
参数：f : Π₀ i, β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
-/
theorem equivFunOnFintype_symm_coe [Fintype ι] (f : Π₀ i, β i) : equivFunOnFintype.symm f = f :=
  Equiv.symm_apply_apply _ _

variable [DecidableEq ι]

/-- The function `single i b : Π₀ i, β i` sends `i` to `b`
and all other points to `0`. -/
/-
**DFinsupp.single** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp`。
形式化陈述：single (i : ι) (b : β i) : Π₀ i, β i
参数：i : ι；b : β i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The function `single i b : Π₀ i, β i` sends `i` to `b`
and all other points to `0`.
-/
def single (i : ι) (b : β i) : Π₀ i, β i :=
  ⟨Pi.single i b,
    Trunc.mk ⟨{i}, fun j => (Decidable.eq_or_ne j i).imp (by simp) fun h => Pi.single_eq_of_ne h _⟩⟩
/-
**DFinsupp.single_eq_pi_single** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：single_eq_pi_single {i b} : ⇑(single i b : Π₀ i, β i) = Pi.single i b
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem single_eq_pi_single {i b} : ⇑(single i b : Π₀ i, β i) = Pi.single i b :=
  rfl

@[simp, grind =]
/-
**DFinsupp.single_apply** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：single_apply {i i' b} : (single i b : Π₀ i, β i) i' = if h : i = i' then E
q.recOn h b else 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFinsupp.single_eq_pi_single`：single_eq_pi_single {i b} : ⇑(single i b :
 Π₀ i, β i) = Pi.single i b
· 使用定理 `Pi.single.eq_1`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) → Ze
ro (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x = Function
.upd…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.update.eq_1`：∀ {α : Sort u} {β : α → Sort v} [inst : DecidableE
q α] (f : (a : α) → β a) (a' : α) (v : β a') (a : α),   Function.update f a' v a
 = if h : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem single_apply {i i' b} :
    (single i b : Π₀ i, β i) i' = if h : i = i' then Eq.recOn h b else 0 := by
  rw [single_eq_pi_single, Pi.single, Function.update]
  simp [@eq_comm _ i i']

@[simp]
/-
**DFinsupp.single_zero** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：single_zero (i) : (single i 0 : Π₀ i, β i) = 0
参数：i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
· 使用定理 `Pi.single_zero`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) → Ze
ro (M i)] [inst_1 : DecidableEq ι] (i : ι), Pi.single i 0 = 0
-/
theorem single_zero (i) : (single i 0 : Π₀ i, β i) = 0 :=
  DFunLike.coe_injective <| Pi.single_zero _
/-
**DFinsupp.single_eq_same** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：single_eq_same {i b} : (single i b : Π₀ i, β i) i = b
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem single_eq_same {i b} : (single i b : Π₀ i, β i) i = b := by
  grind
/-
**DFinsupp.single_eq_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：single_eq_of_ne {i i' b} (h : i' != i) : (single i b : Π₀ i, β i) i' = 0
参数：h : i' != i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem single_eq_of_ne {i i' b} (h : i' ≠ i) : (single i b : Π₀ i, β i) i' = 0 := by
  grind
/-
**DFinsupp.single_injective** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：single_injective {i} : Function.Injective (single i : β i -> Π₀ i, β i)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.single_injective`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι)
 → Zero (M i)] [inst_1 : DecidableEq ι] (i : ι),   Function.Injective (Pi.single
 i)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
theorem single_injective {i} : Function.Injective (single i : β i → Π₀ i, β i) := fun _ _ H =>
  Pi.single_injective i <| DFunLike.coe_injective.eq_iff.mpr H

/-- Like `Finsupp.single_eq_single_iff`, but with a `HEq` due to dependent types -/
/-
**DFinsupp.single_eq_single_iff** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：single_eq_single_iff (i j : ι) (xi : β i) (xj : β j) : DFinsupp.single i x
i = DFinsupp.single j xj ↔ i = j ∧ xi ≍ xj ∨ xi = 0 ∧ xj = 0
参数：i j : ι；xi : β i；xj : β j。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `DFinsupp.single_injective`：single_injective {i} : Function.Injective (si
ngle i : β i -> Π₀ i, β i)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFinsupp.single_eq_of_ne`：single_eq_of_ne {i i' b} (h : i' != i) : (sing
le i b : Π₀ i, β i) i' = 0
· 使用定理 `DFinsupp.single_eq_same`：single_eq_same {i b} : (single i b : Π₀ i, β i)
 i = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `DFinsupp.single_zero`：single_zero (i) : (single i 0 : Π₀ i, β i) = 0

--- 原说明 ---
Like `Finsupp.single_eq_single_iff`, but with a `HEq` due to dependent types
-/
theorem single_eq_single_iff (i j : ι) (xi : β i) (xj : β j) :
    DFinsupp.single i xi = DFinsupp.single j xj ↔ i = j ∧ xi ≍ xj ∨ xi = 0 ∧ xj = 0 := by
  constructor
  · intro h
    by_cases hij : i = j
    · subst hij
      exact Or.inl ⟨rfl, heq_of_eq (DFinsupp.single_injective h)⟩
    · have h_coe : ⇑(DFinsupp.single i xi) = DFinsupp.single j xj := congr_arg (⇑) h
      have hci := congr_fun h_coe i
      have hcj := congr_fun h_coe j
      rw [DFinsupp.single_eq_same] at hci hcj
      rw [DFinsupp.single_eq_of_ne hij] at hci
      rw [DFinsupp.single_eq_of_ne (Ne.symm hij)] at hcj
      exact Or.inr ⟨hci, hcj.symm⟩
  · rintro (⟨rfl, hxi⟩ | ⟨hi, hj⟩)
    · rw [eq_of_heq hxi]
    · rw [hi, hj, DFinsupp.single_zero, DFinsupp.single_zero]

/-- `DFinsupp.single a b` is injective in `a`. For the statement that it is injective in `b`, see
`DFinsupp.single_injective` -/
/-
**DFinsupp.single_left_injective** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：single_left_injective {b : forall i : ι, β i} (h : forall i, b i != 0) : F
unction.Injective (fun i => single i (b i) : ι -> Π₀ i, β i)
参数：h : forall i, b i != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFinsupp.single_eq_single_iff`：single_eq_single_iff (i j : ι) (xi : β i)
 (xj : β j) : DFinsupp.single i xi = DFinsupp.single j xj ↔ i = j ∧ xi ≍ xj ∨ xi
 = 0 ∧ xj = 0

--- 原说明 ---
`DFinsupp.single a b` is injective in `a`. For the statement that it is injectiv
e in `b`, see
`DFinsupp.single_injective`
-/
theorem single_left_injective {b : ∀ i : ι, β i} (h : ∀ i, b i ≠ 0) :
    Function.Injective (fun i => single i (b i) : ι → Π₀ i, β i) := fun _ _ H =>
  (((single_eq_single_iff _ _ _ _).mp H).resolve_right fun hb => h _ hb.1).left

@[simp]
/-
**DFinsupp.single_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：single_eq_zero {i : ι} {xi : β i} : single i xi = 0 ↔ xi = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DFinsupp.single_zero`：single_zero (i) : (single i 0 : Π₀ i, β i) = 0
· 使用定理 `DFinsupp.single_eq_single_iff`：single_eq_single_iff (i j : ι) (xi : β i)
 (xj : β j) : DFinsupp.single i xi = DFinsupp.single j xj ↔ i = j ∧ xi ≍ xj ∨ xi
 = 0 ∧ xj = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem single_eq_zero {i : ι} {xi : β i} : single i xi = 0 ↔ xi = 0 := by
  rw [← single_zero i, single_eq_single_iff]
  simp
/-
**DFinsupp.single_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：single_ne_zero {i : ι} {xi : β i} : single i xi != 0 ↔ xi != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `DFinsupp.single_eq_zero`：single_eq_zero {i : ι} {xi : β i} : single i xi
 = 0 ↔ xi = 0
-/
theorem single_ne_zero {i : ι} {xi : β i} : single i xi ≠ 0 ↔ xi ≠ 0 :=
  single_eq_zero.not
/-
**DFinsupp.filter_single** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：filter_single (p : ι -> Prop) [DecidablePred p] (i : ι) (x : β i) : (singl
e i x).filter p = if p i then single i x else 0
参数：p : ι -> Prop；i : ι；x : β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
-/
theorem filter_single (p : ι → Prop) [DecidablePred p] (i : ι) (x : β i) :
    (single i x).filter p = if p i then single i x else 0 := by
  ext j
  have := apply_ite (fun x : Π₀ i, β i => x j) (p i) (single i x) 0
  dsimp at this
  grind

@[simp]
/-
**DFinsupp.filter_single_pos** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：filter_single_pos {p : ι -> Prop} [DecidablePred p] (i : ι) (x : β i) (h :
 p i) : (single i x).filter p = single i x
参数：i : ι；x : β i；h : p i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFinsupp.filter_single`：filter_single (p : ι -> Prop) [DecidablePred p] 
(i : ι) (x : β i) : (single i x).filter p = if p i then single i x else 0
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem filter_single_pos {p : ι → Prop} [DecidablePred p] (i : ι) (x : β i) (h : p i) :
    (single i x).filter p = single i x := by rw [filter_single, if_pos h]

@[simp]
/-
**DFinsupp.filter_single_neg** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：filter_single_neg {p : ι -> Prop} [DecidablePred p] (i : ι) (x : β i) (h :
 ¬p i) : (single i x).filter p = 0
参数：i : ι；x : β i；h : ¬p i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFinsupp.filter_single`：filter_single (p : ι -> Prop) [DecidablePred p] 
(i : ι) (x : β i) : (single i x).filter p = if p i then single i x else 0
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem filter_single_neg {p : ι → Prop} [DecidablePred p] (i : ι) (x : β i) (h : ¬p i) :
    (single i x).filter p = 0 := by rw [filter_single, if_neg h]

/-- Equality of sigma types is sufficient (but not necessary) to show equality of `DFinsupp`s. -/
/-
**DFinsupp.single_eq_of_sigma_eq** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：single_eq_of_sigma_eq {i j} {xi : β i} {xj : β j} (h : (⟨i, xi⟩ : Sigma β)
 = ⟨j, xj⟩) : DFinsupp.single i xi = DFinsupp.single j xj
参数：h : (⟨i, xi⟩ : Sigma β) = ⟨j, xj⟩。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'

--- 原说明 ---
Equality of sigma types is sufficient (but not necessary) to show equality of `D
Finsupp`s.
-/
theorem single_eq_of_sigma_eq {i j} {xi : β i} {xj : β j} (h : (⟨i, xi⟩ : Sigma β) = ⟨j, xj⟩) :
    DFinsupp.single i xi = DFinsupp.single j xj := by
  cases h
  rfl

@[simp]
/-
**DFinsupp.equivFunOnFintype_single** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：equivFunOnFintype_single [Fintype ι] (i : ι) (m : β i) : (@DFinsupp.equivF
unOnFintype ι β _ _) (DFinsupp.single i m) = Pi.single i m
参数：i : ι；m : β i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem equivFunOnFintype_single [Fintype ι] (i : ι) (m : β i) :
    (@DFinsupp.equivFunOnFintype ι β _ _) (DFinsupp.single i m) = Pi.single i m := rfl

@[simp]
/-
**DFinsupp.equivFunOnFintype_symm_single** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：equivFunOnFintype_symm_single [Fintype ι] (i : ι) (m : β i) : (@DFinsupp.e
quivFunOnFintype ι β _ _).symm (Pi.single i m) = DFinsupp.single i m
参数：i : ι；m : β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFinsupp.equivFunOnFintype_symm_coe`：equivFunOnFintype_symm_coe [Fintype
 ι] (f : Π₀ i, β i) : equivFunOnFintype.symm f = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem equivFunOnFintype_symm_single [Fintype ι] (i : ι) (m : β i) :
    (@DFinsupp.equivFunOnFintype ι β _ _).symm (Pi.single i m) = DFinsupp.single i m := by
  simp only [← single_eq_pi_single, equivFunOnFintype_symm_coe]
/-
**DFinsupp.filter_eq** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：∀ {ι : Type u} {β : ι → Type v} [inst : (i : ι) → Zero (β i)] [inst_1 : De
cidableEq ι] (f : Π₀ (i : ι), β i) (i : ι),   DFinsupp.filter (fun x => i = x) f
 = fun₀ | i => f i
参数：i : ι；β i；f : Π₀ (i : ι), β i；i : ι；fun x => i = x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFinsupp.filter_apply`：filter_apply [forall i, Zero (β i)] (p : ι -> Pro
p) [DecidablePred p] (i : ι) (f : Π₀ i, β i) : f.filter p i = if p i then f i el
se 0
· 使用定理 `DFinsupp.single_apply`：single_apply {i i' b} : (single i b : Π₀ i, β i) 
i' = if h : i = i' then Eq.recOn h b else 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[simp] lemma filter_eq (f : Π₀ i, β i) (i : ι) : f.filter (i = ·) = single i (f i) := by
  ext
  rw [filter_apply, single_apply]
  split
  · subst i
    simp
  · simp
/-
**DFinsupp.filter_eq'** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：∀ {ι : Type u} {β : ι → Type v} [inst : (i : ι) → Zero (β i)] [inst_1 : De
cidableEq ι] (f : Π₀ (i : ι), β i) (i : ι),   DFinsupp.filter (fun x => x = i) f
 = fun₀ | i => f i
参数：i : ι；β i；f : Π₀ (i : ι), β i；i : ι；fun x => x = i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFinsupp.filter.congr_simp`：∀ {ι : Type u} {β : ι → Type v} [inst : (i :
 ι) → Zero (β i)] (p p_1 : ι → Prop),   p = p_1 →     ∀ {inst_1 : DecidablePred 
p} [inst_2 : Dec…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `DFinsupp.filter_eq`：∀ {ι : Type u} {β : ι → Type v} [inst : (i : ι) → Ze
ro (β i)] [inst_1 : DecidableEq ι] (f : Π₀ (i : ι), β i) (i : ι),   DFinsupp.fil
ter (fun…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma filter_eq' (f : Π₀ i, β i) (i : ι) : f.filter (· = i) = single i (f i) := by
  simp [eq_comm]

section SingleAndZipWith

variable [∀ i, Zero (β₁ i)] [∀ i, Zero (β₂ i)]
@[simp]
/-
**DFinsupp.zipWith_single_single** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：zipWith_single_single (f : forall i, β₁ i -> β₂ i -> β i) (hf : forall i, 
f i 0 0 = 0) {i} (b₁ : β₁ i) (b₂ : β₂ i) : zipWith f hf (single i b₁) (single i 
b₂) = single i (f i b₁ b₂)
参数：f : forall i, β₁ i -> β₂ i -> β i；hf : forall i, f i 0 0 = 0；b₁ : β₁ i；b₂ : β
₂ i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zipWith_single_single (f : ∀ i, β₁ i → β₂ i → β i) (hf : ∀ i, f i 0 0 = 0)
    {i} (b₁ : β₁ i) (b₂ : β₂ i) :
    zipWith f hf (single i b₁) (single i b₂) = single i (f i b₁ b₂) := by
  grind

end SingleAndZipWith

/-- Redefine `f i` to be `0`. -/
/-
**DFinsupp.erase** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp`。
形式化陈述：erase (i : ι) (x : Π₀ i, β i) : Π₀ i, β i
参数：i : ι；x : Π₀ i, β i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Redefine `f i` to be `0`.
-/
def erase (i : ι) (x : Π₀ i, β i) : Π₀ i, β i :=
  ⟨fun j ↦ if j = i then 0 else x.1 j,
    x.support'.map fun xs ↦ ⟨xs.1, fun j ↦ (xs.prop j).imp_right (by simp only [·, ite_self])⟩⟩

@[simp, grind =]
/-
**DFinsupp.erase_apply** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：erase_apply {i j : ι} {f : Π₀ i, β i} : (f.erase i) j = if j = i then 0 el
se f j
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem erase_apply {i j : ι} {f : Π₀ i, β i} : (f.erase i) j = if j = i then 0 else f j :=
  rfl
/-
**DFinsupp.erase_same** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：erase_same {i : ι} {f : Π₀ i, β i} : (f.erase i) i = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem erase_same {i : ι} {f : Π₀ i, β i} : (f.erase i) i = 0 := by simp
/-
**DFinsupp.erase_ne** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：erase_ne {i i' : ι} {f : Π₀ i, β i} (h : i' != i) : (f.erase i) i' = f i'
参数：h : i' != i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem erase_ne {i i' : ι} {f : Π₀ i, β i} (h : i' ≠ i) : (f.erase i) i' = f i' := by simp [h]
/-
**DFinsupp.piecewise_single_erase** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：piecewise_single_erase (x : Π₀ i, β i) (i : ι) : (single i (x i)).piecewis
e (x.erase i) {i} = x
参数：x : Π₀ i, β i；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFinsupp.piecewise_apply`：piecewise_apply (i : ι) : x.piecewise y s i = 
if i in s then x i else y i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `DFinsupp.single_eq_same`：single_eq_same {i b} : (single i b : Π₀ i, β i)
 i = b
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `DFinsupp.erase_ne`：erase_ne {i i' : ι} {f : Π₀ i, β i} (h : i' != i) : (
f.erase i) i' = f i'
-/
theorem piecewise_single_erase (x : Π₀ i, β i) (i : ι) :
    (single i (x i)).piecewise (x.erase i) {i} = x := by
  ext j; rw [piecewise_apply]; split_ifs with h
  · rw [(id h : j = i), single_eq_same]
  · exact erase_ne h
/-
**DFinsupp.erase_eq_sub_single** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：erase_eq_sub_single {β : ι -> Type*} [forall i, AddGroup (β i)] (f : Π₀ i,
 β i) (i : ι) : f.erase i = f - single i (f i)
参数：β i；f : Π₀ i, β i；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `DFinsupp.single_apply`：single_apply {i i' b} : (single i b : Π₀ i, β i) 
i' = if h : i = i' then Eq.recOn h b else 0
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `DFinsupp.erase_ne`：erase_ne {i i' : ι} {f : Π₀ i, β i} (h : i' != i) : (
f.erase i) i' = f i'
· 使用定理 `DFinsupp.single_eq_of_ne`：single_eq_of_ne {i i' b} (h : i' != i) : (sing
le i b : Π₀ i, β i) i' = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
-/
theorem erase_eq_sub_single {β : ι → Type*} [∀ i, AddGroup (β i)] (f : Π₀ i, β i) (i : ι) :
    f.erase i = f - single i (f i) := by
  ext j
  rcases eq_or_ne j i with (rfl | h)
  · simp
  · simp [erase_ne h, single_eq_of_ne h]

@[simp]
/-
**DFinsupp.erase_zero** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：erase_zero (i : ι) : erase i (0 : Π₀ i, β i) = 0
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
-/
theorem erase_zero (i : ι) : erase i (0 : Π₀ i, β i) = 0 :=
  ext fun _ => ite_self _

@[simp]
/-
**DFinsupp.filter_ne_eq_erase** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：filter_ne_eq_erase (f : Π₀ i, β i) (i : ι) : f.filter (· != i) = f.erase i
参数：f : Π₀ i, β i；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem filter_ne_eq_erase (f : Π₀ i, β i) (i : ι) : f.filter (· ≠ i) = f.erase i := by
  grind

@[simp]
/-
**DFinsupp.filter_ne_eq_erase'** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：filter_ne_eq_erase' (f : Π₀ i, β i) (i : ι) : f.filter (i != ·) = f.erase 
i
参数：f : Π₀ i, β i；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem filter_ne_eq_erase' (f : Π₀ i, β i) (i : ι) : f.filter (i ≠ ·) = f.erase i := by
  grind
/-
**DFinsupp.erase_single** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：erase_single (j : ι) (i : ι) (x : β i) : (single i x).erase j = if i = j t
hen 0 else single i x
参数：j : ι；i : ι；x : β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DFinsupp.filter_ne_eq_erase`：filter_ne_eq_erase (f : Π₀ i, β i) (i : ι) 
: f.filter (· != i) = f.erase i
· 使用定理 `DFinsupp.filter_single`：filter_single (p : ι -> Prop) [DecidablePred p] 
(i : ι) (x : β i) : (single i x).filter p = if p i then single i x else 0
· 使用定理 `ite_not`：∀ {α : Sort u_1} (p : Prop) [inst : Decidable p] (x y : α), (if
 ¬p then x else y) = if p then y else x
-/
theorem erase_single (j : ι) (i : ι) (x : β i) :
    (single i x).erase j = if i = j then 0 else single i x := by
  rw [← filter_ne_eq_erase, filter_single, ite_not]

@[simp]
/-
**DFinsupp.erase_single_same** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：erase_single_same (i : ι) (x : β i) : (single i x).erase i = 0
参数：i : ι；x : β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFinsupp.erase_single`：erase_single (j : ι) (i : ι) (x : β i) : (single 
i x).erase j = if i = j then 0 else single i x
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem erase_single_same (i : ι) (x : β i) : (single i x).erase i = 0 := by
  rw [erase_single, if_pos rfl]

@[simp]
/-
**DFinsupp.erase_single_ne** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：erase_single_ne {i j : ι} (x : β i) (h : i != j) : (single i x).erase j = 
single i x
参数：x : β i；h : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFinsupp.erase_single`：erase_single (j : ι) (i : ι) (x : β i) : (single 
i x).erase j = if i = j then 0 else single i x
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem erase_single_ne {i j : ι} (x : β i) (h : i ≠ j) : (single i x).erase j = single i x := by
  rw [erase_single, if_neg h]

section Update

variable (f : Π₀ i, β i) (i) (b : β i)

/-- Replace the value of a `Π₀ i, β i` at a given point `i : ι` by a given value `b : β i`.
If `b = 0`, this amounts to removing `i` from the support.
Otherwise, `i` is added to it.

This is the (dependent) finitely-supported version of `Function.update`. -/
/-
**DFinsupp.update** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp`。
形式化陈述：update : Π₀ i, β i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Replace the value of a `Π₀ i, β i` at a given point `i : ι` by a given value `b 
: β i`.
If `b = 0`, this amounts to removing `i` from the support.
Otherwise, `i` is added to it.

This is the (dependent) finitely-supported version of `Function.update`.
-/
def update : Π₀ i, β i :=
  ⟨Function.update f i b,
    f.support'.map fun s =>
      ⟨i ::ₘ s.1, fun j => by
        rcases eq_or_ne i j with (rfl | hi)
        · simp
        · obtain hj | (hj : f j = 0) := s.prop j
          · exact Or.inl (Multiset.mem_cons_of_mem hj)
          · exact Or.inr ((Function.update_of_ne hi.symm b _).trans hj)⟩⟩

variable (j : ι)
/-
**DFinsupp.coe_update** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：∀ {ι : Type u} {β : ι → Type v} [inst : (i : ι) → Zero (β i)] [inst_1 : De
cidableEq ι] (f : Π₀ (i : ι), β i) (i : ι)   (b : β i), ⇑(f.update i b) = Functi
on.update (⇑f) i b
参数：i : ι；β i；f : Π₀ (i : ι), β i；i : ι；b : β i；f.update i b；⇑f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_update : (f.update i b : ∀ i : ι, β i) = Function.update f i b := rfl

@[simp]
/-
**DFinsupp.update_self** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：update_self : f.update i (f i) = f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Function.update_eq_self`：update_eq_self (a : α) (f : forall a, β a) : up
date f a (f a) = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem update_self : f.update i (f i) = f := by
  ext
  simp

@[simp]
/-
**DFinsupp.update_eq_erase** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：update_eq_erase : f.update i 0 = f.erase i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
-/
theorem update_eq_erase : f.update i 0 = f.erase i := by
  ext j
  rcases eq_or_ne i j with (rfl | hi)
  · simp
  · simp [hi.symm]
/-
**DFinsupp.update_eq_single_add_erase** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：update_eq_single_add_erase {β : ι -> Type*} [forall i, AddZeroClass (β i)]
 (f : Π₀ i, β i) (i : ι) (b : β i) : f.update i b = single i b + f.erase i
参数：β i；f : Π₀ i, β i；i : ι；b : β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `DFinsupp.single_apply`：single_apply {i i' b} : (single i b : Π₀ i, β i) 
i' = if h : i = i' then Eq.recOn h b else 0
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem update_eq_single_add_erase {β : ι → Type*} [∀ i, AddZeroClass (β i)] (f : Π₀ i, β i)
    (i : ι) (b : β i) : f.update i b = single i b + f.erase i := by
  ext j
  rcases eq_or_ne i j with (rfl | h)
  · simp
  · simp [h, h.symm]
/-
**DFinsupp.update_eq_erase_add_single** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：update_eq_erase_add_single {β : ι -> Type*} [forall i, AddZeroClass (β i)]
 (f : Π₀ i, β i) (i : ι) (b : β i) : f.update i b = f.erase i + single i b
参数：β i；f : Π₀ i, β i；i : ι；b : β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `DFinsupp.single_apply`：single_apply {i i' b} : (single i b : Π₀ i, β i) 
i' = if h : i = i' then Eq.recOn h b else 0
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem update_eq_erase_add_single {β : ι → Type*} [∀ i, AddZeroClass (β i)] (f : Π₀ i, β i)
    (i : ι) (b : β i) : f.update i b = f.erase i + single i b := by
  ext j
  rcases eq_or_ne i j with (rfl | h)
  · simp
  · simp [h, h.symm]
/-
**DFinsupp.update_eq_sub_add_single** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：update_eq_sub_add_single {β : ι -> Type*} [forall i, AddGroup (β i)] (f : 
Π₀ i, β i) (i : ι) (b : β i) : f.update i b = f - single i (f i) + single i b
参数：β i；f : Π₀ i, β i；i : ι；b : β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFinsupp.update_eq_erase_add_single`：update_eq_erase_add_single {β : ι -
> Type*} [forall i, AddZeroClass (β i)] (f : Π₀ i, β i) (i : ι) (b : β i) : f.up
date i b = f.erase i + si…
· 使用定理 `DFinsupp.erase_eq_sub_single`：erase_eq_sub_single {β : ι -> Type*} [fora
ll i, AddGroup (β i)] (f : Π₀ i, β i) (i : ι) : f.erase i = f - single i (f i)
-/
theorem update_eq_sub_add_single {β : ι → Type*} [∀ i, AddGroup (β i)] (f : Π₀ i, β i) (i : ι)
    (b : β i) : f.update i b = f - single i (f i) + single i b := by
  rw [update_eq_erase_add_single f i b, erase_eq_sub_single f i]

end Update

end Basic

section DecidableEq
variable [DecidableEq ι]

section AddMonoid

variable [∀ i, AddZeroClass (β i)]

@[simp]
/-
**DFinsupp.single_add** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：single_add (i : ι) (b₁ b₂ : β i) : single i (b₁ + b₂) = single i b₁ + sing
le i b₂
参数：i : ι；b₁ b₂ : β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DFinsupp.zipWith_single_single`：zipWith_single_single (f : forall i, β₁ 
i -> β₂ i -> β i) (hf : forall i, f i 0 0 = 0) {i} (b₁ : β₁ i) (b₂ : β₂ i) : zip
With f hf (single i …
-/
theorem single_add (i : ι) (b₁ b₂ : β i) : single i (b₁ + b₂) = single i b₁ + single i b₂ :=
  (zipWith_single_single (fun _ => (· + ·)) _ b₁ b₂).symm

@[simp]
/-
**DFinsupp.erase_add** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：erase_add (i : ι) (f₁ f₂ : Π₀ i, β i) : erase i (f₁ + f₂) = erase i f₁ + e
rase i f₂
参数：i : ι；f₁ f₂ : Π₀ i, β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_zero_add`：∀ {M : Type u_4} [inst : AddZeroClass M] {P : Prop} [inst_
1 : Decidable P] {a b : M},   (if P then 0 else a + b) = (if P then 0 else a) + 
if…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem erase_add (i : ι) (f₁ f₂ : Π₀ i, β i) : erase i (f₁ + f₂) = erase i f₁ + erase i f₂ :=
  ext fun _ => by simp [ite_zero_add]

variable (β)

/-- `DFinsupp.single` as an `AddMonoidHom`. -/
@[simps]
/-
**DFinsupp.singleAddHom** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp`。
形式化陈述：singleAddHom (i : ι) : β i ->+ Π₀ i, β i where toFun
参数：i : ι。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.single_add`：single_add (i : ι) (b₁ b₂ : β i) : single i (b₁ + b
₂) = single i b₁ + single i b₂

--- 原说明 ---
`DFinsupp.single` as an `AddMonoidHom`.
-/
def singleAddHom (i : ι) : β i →+ Π₀ i, β i where
  toFun := single i
  map_zero' := single_zero i
  map_add' := single_add i

/-- `DFinsupp.erase` as an `AddMonoidHom`. -/
@[simps]
/-
**DFinsupp.eraseAddHom** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp`。
形式化陈述：eraseAddHom (i : ι) : (Π₀ i, β i) ->+ Π₀ i, β i where toFun
参数：i : ι。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.erase_add`：erase_add (i : ι) (f₁ f₂ : Π₀ i, β i) : erase i (f₁ 
+ f₂) = erase i f₁ + erase i f₂

--- 原说明 ---
`DFinsupp.erase` as an `AddMonoidHom`.
-/
def eraseAddHom (i : ι) : (Π₀ i, β i) →+ Π₀ i, β i where
  toFun := erase i
  map_zero' := erase_zero i
  map_add' := erase_add i

variable {β}

@[simp]
/-
**DFinsupp.single_neg** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：single_neg {β : ι -> Type v} [forall i, AddGroup (β i)] (i : ι) (x : β i) 
: single i (-x) = -single i x
参数：β i；i : ι；x : β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.map_neg`：∀ {α : Type u_2} {β : Type u_3} [inst : AddGroup α
] [inst_1 : SubtractionMonoid β] (f : α →+ β) (a : α), f (-a) = -f a
-/
theorem single_neg {β : ι → Type v} [∀ i, AddGroup (β i)] (i : ι) (x : β i) :
    single i (-x) = -single i x :=
  (singleAddHom β i).map_neg x

@[simp]
/-
**DFinsupp.single_sub** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：single_sub {β : ι -> Type v} [forall i, AddGroup (β i)] (i : ι) (x y : β i
) : single i (x - y) = single i x - single i y
参数：β i；i : ι；x y : β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.map_sub`：∀ {α : Type u_2} {β : Type u_3} [inst : AddGroup α
] [inst_1 : SubtractionMonoid β] (f : α →+ β) (g h : α),   f (g - h) = f g - f h
-/
theorem single_sub {β : ι → Type v} [∀ i, AddGroup (β i)] (i : ι) (x y : β i) :
    single i (x - y) = single i x - single i y :=
  (singleAddHom β i).map_sub x y

@[simp]
/-
**DFinsupp.erase_neg** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：erase_neg {β : ι -> Type v} [forall i, AddGroup (β i)] (i : ι) (f : Π₀ i, 
β i) : (-f).erase i = -f.erase i
参数：β i；i : ι；f : Π₀ i, β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.map_neg`：∀ {α : Type u_2} {β : Type u_3} [inst : AddGroup α
] [inst_1 : SubtractionMonoid β] (f : α →+ β) (a : α), f (-a) = -f a
-/
theorem erase_neg {β : ι → Type v} [∀ i, AddGroup (β i)] (i : ι) (f : Π₀ i, β i) :
    (-f).erase i = -f.erase i :=
  (eraseAddHom β i).map_neg f

@[simp]
/-
**DFinsupp.erase_sub** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：erase_sub {β : ι -> Type v} [forall i, AddGroup (β i)] (i : ι) (f g : Π₀ i
, β i) : (f - g).erase i = f.erase i - g.erase i
参数：β i；i : ι；f g : Π₀ i, β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.map_sub`：∀ {α : Type u_2} {β : Type u_3} [inst : AddGroup α
] [inst_1 : SubtractionMonoid β] (f : α →+ β) (g h : α),   f (g - h) = f g - f h
-/
theorem erase_sub {β : ι → Type v} [∀ i, AddGroup (β i)] (i : ι) (f g : Π₀ i, β i) :
    (f - g).erase i = f.erase i - g.erase i :=
  (eraseAddHom β i).map_sub f g
/-
**DFinsupp.single_add_erase** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：single_add_erase (i : ι) (f : Π₀ i, β i) : single i (f i) + f.erase i = f
参数：i : ι；f : Π₀ i, β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `DFinsupp.single_apply`：single_apply {i i' b} : (single i b : Π₀ i, β i) 
i' = if h : i = i' then Eq.recOn h b else 0
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_true`：∀ {α : Sort u_1} {x : Decidable True} (t e : α), (if True then 
t else e) = t
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem single_add_erase (i : ι) (f : Π₀ i, β i) : single i (f i) + f.erase i = f :=
  ext fun i' =>
    if h : i = i' then by
      subst h; simp only [add_apply, single_apply, erase_apply, add_zero, dite_eq_ite, if_true]
    else by
      simp only [add_apply, single_apply, erase_apply, dif_neg h, if_neg (Ne.symm h), zero_add]
/-
**DFinsupp.erase_add_single** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：erase_add_single (i : ι) (f : Π₀ i, β i) : f.erase i + single i (f i) = f
参数：i : ι；f : Π₀ i, β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_true`：∀ {α : Sort u_1} {x : Decidable True} (t e : α), (if True then 
t else e) = t
· 使用定理 `DFinsupp.single_apply`：single_apply {i i' b} : (single i b : Π₀ i, β i) 
i' = if h : i = i' then Eq.recOn h b else 0
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem erase_add_single (i : ι) (f : Π₀ i, β i) : f.erase i + single i (f i) = f :=
  ext fun i' =>
    if h : i = i' then by
      subst h; simp only [add_apply, single_apply, erase_apply, zero_add, dite_eq_ite, if_true]
    else by
      simp only [add_apply, single_apply, erase_apply, dif_neg h, if_neg (Ne.symm h), add_zero]
/-
**DFinsupp.induction** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：∀ {ι : Type u} {β : ι → Type v} [inst : DecidableEq ι] [inst_1 : (i : ι) →
 AddZeroClass (β i)]   {p : (Π₀ (i : ι), β i) → Prop} (f : Π₀ (i : ι), β i),   p
 0 → (∀ (i : ι) (b : β i) (f : Π₀ (i : ι), β i), f i = 0 → b ≠ 0 → p f → p ((fun
₀ | i => b) + f)) → p f
参数：i : ι；β i；Π₀ (i : ι), β i；f : Π₀ (i : ι), β i；∀ (i : ι) (b : β i) (f : Π₀ (i 
: ι), β i), f i = 0 → b ≠ 0 → p f → p ((fun₀ | i => b) + f)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Trunc.induction_on`：∀ {α : Sort u_1} {β : Trunc α → Prop} (q : Trunc α),
 (∀ (a : α), β (Trunc.mk a)) → β q
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Multiset.notMem_zero`：notMem_zero (a : α) : a ∉ (0 : Multiset α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFinsupp.single_add_erase`：single_add_erase (i : ι) (f : Π₀ i, β i) : si
ngle i (f i) + f.erase i = f
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `DFinsupp.single_zero`：single_zero (i) : (single i 0 : Π₀ i, β i) = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
protected theorem induction {p : (Π₀ i, β i) → Prop} (f : Π₀ i, β i) (h0 : p 0)
    (ha : ∀ (i b) (f : Π₀ i, β i), f i = 0 → b ≠ 0 → p f → p (single i b + f)) : p f := by
  obtain ⟨f, s⟩ := f
  induction s using Trunc.induction_on with | _ s
  obtain ⟨s, H⟩ := s
  induction s using Multiset.induction_on generalizing f with
  | empty =>
    have : f = 0 := funext fun i => (H i).resolve_left (Multiset.notMem_zero _)
    subst this
    exact h0
  | cons i s ih => ?_
  have H2 : p (erase i ⟨f, Trunc.mk ⟨i ::ₘ s, H⟩⟩) := by
    dsimp only [erase, Trunc.map, Trunc.bind, Trunc.liftOn, Trunc.lift_mk,
      Function.comp, Subtype.coe_mk]
    have H2 : ∀ j, j ∈ s ∨ ite (j = i) 0 (f j) = 0 := by grind
    have H3 : ∀ aux, (⟨fun j : ι => ite (j = i) 0 (f j), Trunc.mk ⟨i ::ₘ s, aux⟩⟩ : Π₀ i, β i) =
        ⟨fun j : ι => ite (j = i) 0 (f j), Trunc.mk ⟨s, H2⟩⟩ :=
      fun _ ↦ ext fun _ => rfl
    rw [H3]
    apply ih
  have H3 : single i _ + _ = (⟨f, Trunc.mk ⟨i ::ₘ s, H⟩⟩ : Π₀ i, β i) := single_add_erase _ _
  rw [← H3]
  change p (single i (f i) + _)
  rcases Classical.em (f i = 0) with h | h
  · rw [h, single_zero, zero_add]
    exact H2
  grind
/-
**DFinsupp.induction** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：∀ {ι : Type u} {β : ι → Type v} [inst : DecidableEq ι] [inst_1 : (i : ι) →
 AddZeroClass (β i)]   {p : (Π₀ (i : ι), β i) → Prop} (f : Π₀ (i : ι), β i),   p
 0 → (∀ (i : ι) (b : β i) (f : Π₀ (i : ι), β i), f i = 0 → b ≠ 0 → p f → p ((fun
₀ | i => b) + f)) → p f
参数：i : ι；β i；Π₀ (i : ι), β i；f : Π₀ (i : ι), β i；∀ (i : ι) (b : β i) (f : Π₀ (i 
: ι), β i), f i = 0 → b ≠ 0 → p f → p ((fun₀ | i => b) + f)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Trunc.induction_on`：∀ {α : Sort u_1} {β : Trunc α → Prop} (q : Trunc α),
 (∀ (a : α), β (Trunc.mk a)) → β q
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Multiset.notMem_zero`：notMem_zero (a : α) : a ∉ (0 : Multiset α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFinsupp.single_add_erase`：single_add_erase (i : ι) (f : Π₀ i, β i) : si
ngle i (f i) + f.erase i = f
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `DFinsupp.single_zero`：single_zero (i) : (single i 0 : Π₀ i, β i) = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem induction₂ {p : (Π₀ i, β i) → Prop} (f : Π₀ i, β i) (h0 : p 0)
    (ha : ∀ (i b) (f : Π₀ i, β i), f i = 0 → b ≠ 0 → p f → p (f + single i b)) : p f :=
  DFinsupp.induction f h0 fun i b f h1 h2 h3 =>
    have h4 : f + single i b = single i b + f := by
      ext j; by_cases H : i = j
      · subst H
        simp [h1]
      · simp [H]
    Eq.recOn h4 <| ha i b f h1 h2 h3

end AddMonoid

@[simp]
/-
**DFinsupp.mk_add** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：mk_add [forall i, AddZeroClass (β i)] {s : Finset ι} {x y : forall i : (↑s
 : Set ι), β i} : mk s (x + y) = mk s x + mk s y
参数：β i；↑s : Set ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem mk_add [∀ i, AddZeroClass (β i)] {s : Finset ι} {x y : ∀ i : (↑s : Set ι), β i} :
    mk s (x + y) = mk s x + mk s y :=
  ext fun i => by simp only [add_apply, mk_apply]; split_ifs <;> [rfl; rw [zero_add]]

@[simp]
/-
**DFinsupp.mk_zero** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：mk_zero [forall i, Zero (β i)] {s : Finset ι} : mk s (0 : forall i : (↑s :
 Set ι), β i.1) = 0
参数：β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem mk_zero [∀ i, Zero (β i)] {s : Finset ι} : mk s (0 : ∀ i : (↑s : Set ι), β i.1) = 0 :=
  ext fun i => by simp only [mk_apply]; split_ifs <;> rfl

@[simp]
/-
**DFinsupp.mk_neg** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：mk_neg [forall i, AddGroup (β i)] {s : Finset ι} {x : forall i : (↑s : Set
 ι), β i.1} : mk s (-x) = -mk s x
参数：β i；↑s : Set ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
-/
theorem mk_neg [∀ i, AddGroup (β i)] {s : Finset ι} {x : ∀ i : (↑s : Set ι), β i.1} :
    mk s (-x) = -mk s x :=
  ext fun i => by simp only [neg_apply, mk_apply]; split_ifs <;> [rfl; rw [neg_zero]]

@[simp]
/-
**DFinsupp.mk_sub** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：mk_sub [forall i, AddGroup (β i)] {s : Finset ι} {x y : forall i : (↑s : S
et ι), β i.1} : mk s (x - y) = mk s x - mk s y
参数：β i；↑s : Set ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
-/
theorem mk_sub [∀ i, AddGroup (β i)] {s : Finset ι} {x y : ∀ i : (↑s : Set ι), β i.1} :
    mk s (x - y) = mk s x - mk s y :=
  ext fun i => by simp only [sub_apply, mk_apply]; split_ifs <;> [rfl; rw [sub_zero]]

/-- If `s` is a subset of `ι` then `mk_addGroupHom s` is the canonical additive
group homomorphism from $\prod_{i\in s}\beta_i$ to $\prod_{\mathtt{i : \iota}}\beta_i$. -/
/-
**DFinsupp.mkAddGroupHom** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp`。
形式化陈述：mkAddGroupHom [forall i, AddGroup (β i)] (s : Finset ι) : (forall i : (s :
 Set ι), β ↑i) ->+ Π₀ i : ι, β i where toFun
参数：β i；s : Finset ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `s` is a subset of `ι` then `mk_addGroupHom s` is the canonical additive
group homomorphism from $\prod_{i\in s}\beta_i$ to $\prod_{\mathtt{i : \iota}}\b
eta_i$.
-/
def mkAddGroupHom [∀ i, AddGroup (β i)] (s : Finset ι) :
    (∀ i : (s : Set ι), β ↑i) →+ Π₀ i : ι, β i where
  toFun := mk s
  map_zero' := mk_zero
  map_add' _ _ := mk_add

section SupportBasic

variable [∀ i, Zero (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)]

/-- Set `{i | f x ≠ 0}` as a `Finset`. -/
/-
**DFinsupp.support** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp`。
形式化陈述：support (f : Π₀ i, β i) : Finset ι
参数：f : Π₀ i, β i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Set `{i | f x ≠ 0}` as a `Finset`.
-/
def support (f : Π₀ i, β i) : Finset ι :=
  (f.support'.lift fun xs => (Multiset.toFinset xs.1).filter fun i => f i ≠ 0) <| by
    rintro ⟨sx, hx⟩ ⟨sy, hy⟩
    dsimp only [Subtype.coe_mk, toFun_eq_coe] at *
    ext i; constructor
    · intro H
      rcases Finset.mem_filter.1 H with ⟨_, h⟩
      exact Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2 <| (hy i).resolve_right h, h⟩
    · intro H
      rcases Finset.mem_filter.1 H with ⟨_, h⟩
      exact Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2 <| (hx i).resolve_right h, h⟩

@[simp]
/-
**DFinsupp.support_mk_subset** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：support_mk_subset {s : Finset ι} {x : forall i : (↑s : Set ι), β i.1} : (m
k s x).support subseteq s
参数：↑s : Set ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_toFinset`：mem_toFinset {a : α} {s : Multiset α} : a in s.to
Finset ↔ a in s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
-/
theorem support_mk_subset {s : Finset ι} {x : ∀ i : (↑s : Set ι), β i.1} : (mk s x).support ⊆ s :=
  fun _ H => Multiset.mem_toFinset.1 (Finset.mem_filter.1 H).1

@[simp]
/-
**DFinsupp.support_mk'_subset** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：∀ {ι : Type u} {β : ι → Type v} [inst : DecidableEq ι] [inst_1 : (i : ι) →
 Zero (β i)]   [inst_2 : (i : ι) → (x : β i) → Decidable (x ≠ 0)] {f : (i : ι) →
 β i} {s : Multiset ι}   {h : ∀ (i : ι), i ∈ s ∨ f i = 0}, { toFun := f, support
' := Trunc.mk ⟨s, h⟩ }.support ⊆ s.toFinset
参数：i : ι；β i；i : ι；x : β i；x ≠ 0；i : ι；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_toFinset`：mem_toFinset {a : α} {s : Multiset α} : a in s.to
Finset ↔ a in s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.toFinset_dedup`：toFinset_dedup (m : Multiset α) : m.dedup.toFin
set = m.toFinset
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
-/
theorem support_mk'_subset {f : ∀ i, β i} {s : Multiset ι} {h} :
    (mk' f <| Trunc.mk ⟨s, h⟩).support ⊆ s.toFinset := fun i H =>
  Multiset.mem_toFinset.1 <| by simpa using (Finset.mem_filter.1 H).1

@[simp, grind =]
/-
**DFinsupp.mem_support_toFun** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：mem_support_toFun (f : Π₀ i, β i) (i) : i in f.support ↔ f i != 0
参数：f : Π₀ i, β i；i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Trunc.induction_on`：∀ {α : Sort u_1} {β : Trunc α → Prop} (q : Trunc α),
 (∀ (a : α), β (Trunc.mk a)) → β q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `Multiset.mem_toFinset`：mem_toFinset {a : α} {s : Multiset α} : a in s.to
Finset ↔ a in s
· 使用定理 `DFinsupp.coe_mk'`：∀ {ι : Type u} {β : ι → Type v} [inst : (i : ι) → Zero
 (β i)] (f : (i : ι) → β i)   (s : Trunc { s // ∀ (i : ι), i ∈ s ∨ f i = 0 }), ⇑
{ toFu…
-/
theorem mem_support_toFun (f : Π₀ i, β i) (i) : i ∈ f.support ↔ f i ≠ 0 := by
  obtain ⟨f, s⟩ := f
  induction s using Trunc.induction_on with | _ s
  dsimp only [support, Trunc.lift_mk]
  rw [Finset.mem_filter, Multiset.mem_toFinset, coe_mk']
  grind
/-
**DFinsupp.eq_mk_support** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：eq_mk_support (f : Π₀ i, β i) : f = mk f.support fun i => f i
参数：f : Π₀ i, β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Classical.ite_not`：∀ {α : Sort u_1} (p : Prop) [inst : Decidable ¬p] (x 
y : α), (if ¬p then x else y) = if p then y else x
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem eq_mk_support (f : Π₀ i, β i) : f = mk f.support fun i => f i := by aesop

/-- Equivalence between dependent functions with finite support `s : Finset ι` and functions
`∀ i, {x : β i // x ≠ 0}`. -/
@[simps]
/-
**DFinsupp.subtypeSupportEqEquiv** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp`。
形式化陈述：subtypeSupportEqEquiv (s : Finset ι) : {f : Π₀ i, β i // f.support = s} ≃ 
forall i : s, {x : β i // x != 0} where toFun | ⟨f, hf⟩ => fun ⟨i, hi⟩ => ⟨f i, 
(f.mem_support_toFun i).1 hf.symm ▸ hi⟩ invFun f
参数：s : Finset ι。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivalence between dependent functions with finite support `s : Finset ι` and f
unctions
`∀ i, {x : β i // x ≠ 0}`.
-/
def subtypeSupportEqEquiv (s : Finset ι) :
    {f : Π₀ i, β i // f.support = s} ≃ ∀ i : s, {x : β i // x ≠ 0} where
  toFun | ⟨f, hf⟩ => fun ⟨i, hi⟩ ↦ ⟨f i, (f.mem_support_toFun i).1 <| hf.symm ▸ hi⟩
  invFun f := ⟨mk s fun i ↦ (f i).1, Finset.ext fun i ↦ by
    -- TODO: `simp` fails to use `(f _).2` inside `∃ _, _`
    calc
      i ∈ support (mk s fun i ↦ (f i).1) ↔ ∃ h : i ∈ s, (f ⟨i, h⟩).1 ≠ 0 := by simp
      _ ↔ ∃ _ : i ∈ s, True := exists_congr fun h ↦ (iff_true _).mpr (f _).2
      _ ↔ i ∈ s := by simp⟩
  left_inv := by
    rintro ⟨f, rfl⟩
    ext i
    simpa using Eq.symm
  right_inv f := by
    #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
    (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal.
    It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in the new
    canonicalizer; a minimization would help. The original proof was: `grind` -/
    simp

/-- Equivalence between all dependent finitely supported functions `f : Π₀ i, β i` and type
of pairs `⟨s : Finset ι, f : ∀ i : s, {x : β i // x ≠ 0}⟩`. -/
@[simps! apply_fst apply_snd_coe]
/-
**DFinsupp.sigmaFinsetFunEquiv** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp`。
形式化陈述：sigmaFinsetFunEquiv : (Π₀ i, β i) ≃ Σ s : Finset ι, forall i : s, {x : β i
 // x != 0}
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Equivalence between all dependent finitely supported functions `f : Π₀ i, β i` a
nd type
of pairs `⟨s : Finset ι, f : ∀ i : s, {x : β i // x ≠ 0}⟩`.
-/
def sigmaFinsetFunEquiv : (Π₀ i, β i) ≃ Σ s : Finset ι, ∀ i : s, {x : β i // x ≠ 0} :=
  (Equiv.sigmaFiberEquiv DFinsupp.support).symm.trans (.sigmaCongrRight subtypeSupportEqEquiv)

@[simp]
/-
**DFinsupp.support_zero** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：support_zero : (0 : Π₀ i, β i).support = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem support_zero : (0 : Π₀ i, β i).support = ∅ :=
  rfl
/-
**DFinsupp.mem_support_iff** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：mem_support_iff {f : Π₀ i, β i} {i : ι} : i in f.support ↔ f i != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.mem_support_toFun`：mem_support_toFun (f : Π₀ i, β i) (i) : i in
 f.support ↔ f i != 0
-/
theorem mem_support_iff {f : Π₀ i, β i} {i : ι} : i ∈ f.support ↔ f i ≠ 0 :=
  f.mem_support_toFun _
/-
**DFinsupp.notMem_support_iff** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：notMem_support_iff {f : Π₀ i, β i} {i : ι} : i ∉ f.support ↔ f i = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_iff_comm`：not_iff_comm : (¬a ↔ b) ↔ (¬b ↔ a)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `DFinsupp.mem_support_iff`：mem_support_iff {f : Π₀ i, β i} {i : ι} : i in
 f.support ↔ f i != 0
-/
theorem notMem_support_iff {f : Π₀ i, β i} {i : ι} : i ∉ f.support ↔ f i = 0 :=
  not_iff_comm.1 mem_support_iff.symm

@[simp]
/-
**DFinsupp.support_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：support_eq_empty {f : Π₀ i, β i} : f.support = ∅ ↔ f = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `DFinsupp.support.congr_simp`：∀ {ι : Type u} {β : ι → Type v} [inst : Dec
idableEq ι] [inst_1 : (i : ι) → Zero (β i)]   {inst_2 : (i : ι) → (x : β i) → De
cidable (x ≠ 0)} …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem support_eq_empty {f : Π₀ i, β i} : f.support = ∅ ↔ f = 0 :=
  ⟨fun H => ext <| by simpa [Finset.ext_iff] using H, by simp +contextual⟩
/-
**DFinsupp.decidableZero** 是 Mathlib 中的一个实例，位于命名空间 `DFinsupp`。
形式化陈述：decidableZero [forall (i) (x : β i), Decidable (x = 0)] (f : Π₀ i, β i) : 
Decidable (f = 0)
参数：i；x : β i；x = 0；f : Π₀ i, β i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableZero [∀ (i) (x : β i), Decidable (x = 0)] (f : Π₀ i, β i) : Decidable (f = 0) :=
  f.support'.recOnSubsingleton <| fun s =>
    decidable_of_iff (∀ i ∈ s.val, f i = 0) <| by
      constructor
      case mpr => rintro rfl _ _; rfl
      case mp =>
        intro hs₁; ext i
        -- This instance prevent consuming `DecidableEq ι` in the next `by_cases`.
        let := Classical.propDecidable
        by_cases hs₂ : i ∈ s.val
        case pos => exact hs₁ _ hs₂
        case neg => exact (s.prop i).resolve_left hs₂
/-
**DFinsupp.support_subset_iff** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：support_subset_iff {s : Set ι} {f : Π₀ i, β i} : ↑f.support subseteq s ↔ f
orall i ∉ s, f i = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `not_imp_comm`：not_imp_comm : ¬a -> b ↔ ¬b -> a
-/
theorem support_subset_iff {s : Set ι} {f : Π₀ i, β i} : ↑f.support ⊆ s ↔ ∀ i ∉ s, f i = 0 := by
  simpa [Set.subset_def] using forall_congr' fun i => not_imp_comm

@[simp]
/-
**DFinsupp.support_single** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：support_single {i : ι} {b : β i} (hb : b != 0) : (single i b).support = {i
}
参数：hb : b != 0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem support_single {i : ι} {b : β i} (hb : b ≠ 0) : (single i b).support = {i} := by
  grind

@[deprecated (since := "2026-05-05")] alias support_single_ne_zero := support_single
/-
**DFinsupp.support_single_subset** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：support_single_subset {i : ι} {b : β i} : (single i b).support subseteq {i
}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.support_mk'_subset`：∀ {ι : Type u} {β : ι → Type v} [inst : Dec
idableEq ι] [inst_1 : (i : ι) → Zero (β i)]   [inst_2 : (i : ι) → (x : β i) → De
cidable (x ≠ 0)] …
-/
theorem support_single_subset {i : ι} {b : β i} : (single i b).support ⊆ {i} :=
  support_mk'_subset

section MapRangeAndZipWith

variable [∀ i, Zero (β₁ i)] [∀ i, Zero (β₂ i)]

/-
**DFinsupp.mapRange_def** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：mapRange_def [forall (i) (x : β₁ i), Decidable (x != 0)] {f : forall i, β₁
 i -> β₂ i} {hf : forall i, f i 0 = 0} {g : Π₀ i, β₁ i} : mapRange f hf g = mk g
.support fun i => f i.1 (g i.1)
参数：i；x : β₁ i；x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Classical.ite_not`：∀ {α : Sort u_1} (p : Prop) [inst : Decidable ¬p] (x 
y : α), (if ¬p then x else y) = if p then y else x
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem mapRange_def [∀ (i) (x : β₁ i), Decidable (x ≠ 0)] {f : ∀ i, β₁ i → β₂ i}
    {hf : ∀ i, f i 0 = 0} {g : Π₀ i, β₁ i} :
    mapRange f hf g = mk g.support fun i => f i.1 (g i.1) := by
  ext
  simp_all

@[simp]
/-
**DFinsupp.mapRange_single** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：mapRange_single {f : forall i, β₁ i -> β₂ i} {hf : forall i, f i 0 = 0} {i
 : ι} {b : β₁ i} : mapRange f hf (single i b) = single i (f i b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `DFinsupp.single_apply`：single_apply {i i' b} : (single i b : Π₀ i, β i) 
i' = if h : i = i' then Eq.recOn h b else 0
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
theorem mapRange_single {f : ∀ i, β₁ i → β₂ i} {hf : ∀ i, f i 0 = 0} {i : ι} {b : β₁ i} :
    mapRange f hf (single i b) = single i (f i b) :=
  DFinsupp.ext fun i' => by
    by_cases h : i = i'
    · subst i'
      simp
    · simp [h, hf]

omit [DecidableEq ι] in
/-
**DFinsupp.mapRange_injective** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：mapRange_injective (f : forall i, β₁ i -> β₂ i) (hf : forall i, f i 0 = 0)
 : Function.Injective (mapRange f hf) ↔ forall i, Function.Injective (f i)
参数：f : forall i, β₁ i -> β₂ i；hf : forall i, f i 0 = 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.single_injective`：single_injective {i} : Function.Injective (si
ngle i : β i -> Π₀ i, β i)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFinsupp.mapRange_single`：mapRange_single {f : forall i, β₁ i -> β₂ i} {
hf : forall i, f i 0 = 0} {i : ι} {b : β₁ i} : mapRange f hf (single i b) = sing
le i (f i b)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
-/
theorem mapRange_injective (f : ∀ i, β₁ i → β₂ i) (hf : ∀ i, f i 0 = 0) :
    Function.Injective (mapRange f hf) ↔ ∀ i, Function.Injective (f i) := by
  classical exact ⟨fun h i x y eq ↦ single_injective (@h (single i x) (single i y) <| by
    simpa using congr_arg _ eq), fun h _ _ eq ↦ DFinsupp.ext fun i ↦ h i congr($eq i)⟩

set_option backward.isDefEq.respectTransparency false in
omit [DecidableEq ι] in
/-
**DFinsupp.mapRange_surjective** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：mapRange_surjective (f : forall i, β₁ i -> β₂ i) (hf : forall i, f i 0 = 0
) : Function.Surjective (mapRange f hf) ↔ forall i, Function.Surjective (f i)
参数：f : forall i, β₁ i -> β₂ i；hf : forall i, f i 0 = 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `DFinsupp.single_apply`：single_apply {i i' b} : (single i b : Π₀ i, β i) 
i' = if h : i = i' then Eq.recOn h b else 0
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Or.imp_right`：∀ {b c a : Prop}, (b → c) → a ∨ b → a ∨ c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem mapRange_surjective (f : ∀ i, β₁ i → β₂ i) (hf : ∀ i, f i 0 = 0) :
    Function.Surjective (mapRange f hf) ↔ ∀ i, Function.Surjective (f i) := by
  classical
  refine ⟨fun h i u ↦ ?_, fun h x ↦ ?_⟩
  · obtain ⟨x, hx⟩ := h (single i u)
    exact ⟨x i, by simpa using congr($hx i)⟩
  · obtain ⟨x, s, hs⟩ := x
    have (i : ι) : ∃ u : β₁ i, f i u = x i ∧ (x i = 0 → u = 0) :=
      (eq_or_ne (x i) 0).elim
        (fun h ↦ ⟨0, (hf i).trans h.symm, fun _ ↦ rfl⟩)
        (fun h' ↦ by
          obtain ⟨u, hu⟩ := h i (x i)
          exact ⟨u, hu, fun h'' ↦ (h' h'').elim⟩)
    choose y hy using this
    refine ⟨⟨y, Trunc.mk ⟨s, fun i ↦ ?_⟩⟩, ext fun i ↦ ?_⟩
    · exact (hs i).imp_right (hy i).2
    · simp [(hy i).1]

variable [∀ (i) (x : β₁ i), Decidable (x ≠ 0)] [∀ (i) (x : β₂ i), Decidable (x ≠ 0)]
/-
**DFinsupp.support_mapRange** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：support_mapRange {f : forall i, β₁ i -> β₂ i} {hf : forall i, f i 0 = 0} {
g : Π₀ i, β₁ i} : (mapRange f hf g).support subseteq g.support
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFinsupp.support.congr_simp`：∀ {ι : Type u} {β : ι → Type v} [inst : Dec
idableEq ι] [inst_1 : (i : ι) → Zero (β i)]   {inst_2 : (i : ι) → (x : β i) → De
cidable (x ≠ 0)} …
· 使用定理 `DFinsupp.mapRange_def`：mapRange_def [forall (i) (x : β₁ i), Decidable (x
 != 0)] {f : forall i, β₁ i -> β₂ i} {hf : forall i, f i 0 = 0} {g : Π₀ i, β₁ i}
 : mapRange…
-/
theorem support_mapRange {f : ∀ i, β₁ i → β₂ i} {hf : ∀ i, f i 0 = 0} {g : Π₀ i, β₁ i} :
    (mapRange f hf g).support ⊆ g.support := by simp [mapRange_def]
/-
**DFinsupp.zipWith_def** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：zipWith_def {ι : Type u} {β : ι -> Type v} {β₁ : ι -> Type v₁} {β₂ : ι -> 
Type v₂} [dec : DecidableEq ι] [forall i : ι, Zero (β i)] [forall i : ι, Zero (β
₁ i)] [forall i : ι, Zero (β₂ i)] [forall (i : ι) (x : β₁ i), Decidable (x != 0)
] [forall (i : ι) (x : β₂ i), Decidable (x != 0)] {f : forall i, β₁ i -> β₂ i ->
 β i} {hf : forall i, f i 0 0 = 0} {g₁ : Π₀ i, β₁ i} {g₂ : Π₀ i, β₂ i} : zipWith
 f hf g₁ g₂ = mk (g₁.support union g₂.support) fun i => f i.1 (g₁ i.1) (g₂ i.1)
参数：β i；β₁ i；β₂ i；i : ι；x : β₁ i；x != 0；i : ι；x : β₂ i；x != 0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zipWith_def {ι : Type u} {β : ι → Type v} {β₁ : ι → Type v₁} {β₂ : ι → Type v₂}
    [dec : DecidableEq ι] [∀ i : ι, Zero (β i)] [∀ i : ι, Zero (β₁ i)] [∀ i : ι, Zero (β₂ i)]
    [∀ (i : ι) (x : β₁ i), Decidable (x ≠ 0)] [∀ (i : ι) (x : β₂ i), Decidable (x ≠ 0)]
    {f : ∀ i, β₁ i → β₂ i → β i} {hf : ∀ i, f i 0 0 = 0} {g₁ : Π₀ i, β₁ i} {g₂ : Π₀ i, β₂ i} :
    zipWith f hf g₁ g₂ = mk (g₁.support ∪ g₂.support) fun i => f i.1 (g₁ i.1) (g₂ i.1) := by
  grind
/-
**DFinsupp.support_zipWith** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：support_zipWith {f : forall i, β₁ i -> β₂ i -> β i} {hf : forall i, f i 0 
0 = 0} {g₁ : Π₀ i, β₁ i} {g₂ : Π₀ i, β₂ i} : (zipWith f hf g₁ g₂).support subset
eq g₁.support union g₂.support
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem support_zipWith {f : ∀ i, β₁ i → β₂ i → β i} {hf : ∀ i, f i 0 0 = 0} {g₁ : Π₀ i, β₁ i}
    {g₂ : Π₀ i, β₂ i} : (zipWith f hf g₁ g₂).support ⊆ g₁.support ∪ g₂.support := by
  grind

end MapRangeAndZipWith

/-
**DFinsupp.erase_def** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：erase_def (i : ι) (f : Π₀ i, β i) : f.erase i = mk (f.support.erase i) fun
 j => f j.1
参数：i : ι；f : Π₀ i, β i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem erase_def (i : ι) (f : Π₀ i, β i) : f.erase i = mk (f.support.erase i) fun j => f j.1 := by
  grind

@[simp]
/-
**DFinsupp.support_erase** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：support_erase (i : ι) (f : Π₀ i, β i) : (f.erase i).support = f.support.er
ase i
参数：i : ι；f : Π₀ i, β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem support_erase (i : ι) (f : Π₀ i, β i) : (f.erase i).support = f.support.erase i := by
  ext
  simp
/-
**DFinsupp.support_update_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：support_update_ne_zero (f : Π₀ i, β i) (i : ι) {b : β i} (h : b != 0) : su
pport (f.update i b) = insert i f.support
参数：f : Π₀ i, β i；i : ι；h : b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
-/
theorem support_update_ne_zero (f : Π₀ i, β i) (i : ι) {b : β i} (h : b ≠ 0) :
    support (f.update i b) = insert i f.support := by
  ext j
  rcases eq_or_ne i j with (rfl | hi)
  · simp [h]
  · simp [hi.symm]
/-
**DFinsupp.support_update** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：support_update (f : Π₀ i, β i) (i : ι) (b : β i) [Decidable (b = 0)] : sup
port (f.update i b) = if b = 0 then support (f.erase i) else insert i f.support
参数：f : Π₀ i, β i；i : ι；b : β i；b = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `DFinsupp.support.congr_simp`：∀ {ι : Type u} {β : ι → Type v} [inst : Dec
idableEq ι] [inst_1 : (i : ι) → Zero (β i)]   {inst_2 : (i : ι) → (x : β i) → De
cidable (x ≠ 0)} …
· 使用定理 `DFinsupp.update_eq_erase`：update_eq_erase : f.update i 0 = f.erase i
· 使用定理 `DFinsupp.support_erase`：support_erase (i : ι) (f : Π₀ i, β i) : (f.erase
 i).support = f.support.erase i
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `DFinsupp.support_update_ne_zero`：support_update_ne_zero (f : Π₀ i, β i) 
(i : ι) {b : β i} (h : b != 0) : support (f.update i b) = insert i f.support
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem support_update (f : Π₀ i, β i) (i : ι) (b : β i) [Decidable (b = 0)] :
    support (f.update i b) = if b = 0 then support (f.erase i) else insert i f.support := by
  ext j
  split_ifs with hb
  · subst hb
    simp [update_eq_erase, support_erase]
  · rw [support_update_ne_zero f _ hb]

section FilterAndSubtypeDomain

variable {p : ι → Prop} [DecidablePred p]

/-
**DFinsupp.filter_def** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：filter_def (f : Π₀ i, β i) : f.filter p = mk (f.support.filter p) fun i =>
 f i.1
参数：f : Π₀ i, β i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem filter_def (f : Π₀ i, β i) : f.filter p = mk (f.support.filter p) fun i => f i.1 := by
  grind

@[simp]
/-
**DFinsupp.support_filter** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：support_filter (f : Π₀ i, β i) : (f.filter p).support = {x in f.support | 
p x}
参数：f : Π₀ i, β i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem support_filter (f : Π₀ i, β i) : (f.filter p).support = {x ∈ f.support | p x} := by
  grind
/-
**DFinsupp.subtypeDomain_def** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：subtypeDomain_def (f : Π₀ i, β i) : f.subtypeDomain p = mk (f.support.subt
ype p) fun i => f i
参数：f : Π₀ i, β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `not_true_eq_false`：(¬True) = False
-/
theorem subtypeDomain_def (f : Π₀ i, β i) :
    f.subtypeDomain p = mk (f.support.subtype p) fun i => f i := by
  ext i; by_cases h2 : f i ≠ 0 <;> try simp at h2; simp [h2]

@[simp]
/-
**DFinsupp.support_subtypeDomain** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：support_subtypeDomain {f : Π₀ i, β i} : (subtypeDomain p f).support = f.su
pport.subtype p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem support_subtypeDomain {f : Π₀ i, β i} :
    (subtypeDomain p f).support = f.support.subtype p := by
  ext
  simp

end FilterAndSubtypeDomain

end SupportBasic

/-
**DFinsupp.support_add** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：support_add [forall i, AddZeroClass (β i)] [forall (i) (x : β i), Decidabl
e (x != 0)] {g₁ g₂ : Π₀ i, β i} : (g₁ + g₂).support subseteq g₁.support union g₂
.support
参数：β i；i；x : β i；x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.support_zipWith`：support_zipWith {f : forall i, β₁ i -> β₂ i ->
 β i} {hf : forall i, f i 0 0 = 0} {g₁ : Π₀ i, β₁ i} {g₂ : Π₀ i, β₂ i} : (zipWit
h f hf g₁ g₂).…
-/
theorem support_add [∀ i, AddZeroClass (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)]
    {g₁ g₂ : Π₀ i, β i} : (g₁ + g₂).support ⊆ g₁.support ∪ g₂.support :=
  support_zipWith

@[simp]
/-
**DFinsupp.support_neg** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：support_neg [forall i, AddGroup (β i)] [forall (i) (x : β i), Decidable (x
 != 0)] {f : Π₀ i, β i} : support (-f) = support f
参数：β i；i；x : β i；x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem support_neg [∀ i, AddGroup (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)] {f : Π₀ i, β i} :
    support (-f) = support f := by ext; simp
/-
**DFinsupp.** 是 Mathlib 中的一个实例，位于命名空间 `DFinsupp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, Zero (β i)] [∀ i, DecidableEq (β i)] : DecidableEq (Π₀ i, β i) := fun f g =>
  decidable_of_iff (f.support = g.support ∧ ∀ i ∈ f.support, f i = g i)
    ⟨fun ⟨h₁, h₂⟩ => ext fun i => if h : i ∈ f.support then h₂ i h else by
      have hf : f i = 0 := by rwa [mem_support_iff, not_not] at h
      have hg : g i = 0 := by rwa [h₁, mem_support_iff, not_not] at h
      rw [hf, hg],
     by rintro rfl; simp⟩

end DecidableEq

section Equiv

open Finset

variable {κ : Type*}

/-- Reindexing (and possibly removing) terms of a dfinsupp. -/
/-
**DFinsupp.comapDomain** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp`。
形式化陈述：comapDomain [forall i, Zero (β i)] (h : κ -> ι) (hh : Function.Injective h
) (f : Π₀ i, β i) : Π₀ k, β (h k) where toFun x
参数：β i；h : κ -> ι；hh : Function.Injective h；f : Π₀ i, β i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reindexing (and possibly removing) terms of a dfinsupp.
-/
noncomputable def comapDomain [∀ i, Zero (β i)] (h : κ → ι) (hh : Function.Injective h)
    (f : Π₀ i, β i) : Π₀ k, β (h k) where
  toFun x := f (h x)
  support' :=
    f.support'.map fun s =>
      ⟨(s.1.finite_toSet.preimage hh.injOn).toFinset.val, fun x =>
        (s.prop (h x)).imp_left fun hx => (Set.Finite.mem_toFinset _).mpr <| hx⟩

@[simp]
/-
**DFinsupp.comapDomain_apply** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：comapDomain_apply [forall i, Zero (β i)] (h : κ -> ι) (hh : Function.Injec
tive h) (f : Π₀ i, β i) (k : κ) : comapDomain h hh f k = f (h k)
参数：β i；h : κ -> ι；hh : Function.Injective h；f : Π₀ i, β i；k : κ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comapDomain_apply [∀ i, Zero (β i)] (h : κ → ι) (hh : Function.Injective h) (f : Π₀ i, β i)
    (k : κ) : comapDomain h hh f k = f (h k) :=
  rfl

@[simp]
/-
**DFinsupp.comapDomain_zero** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：comapDomain_zero [forall i, Zero (β i)] (h : κ -> ι) (hh : Function.Inject
ive h) : comapDomain h hh (0 : Π₀ i, β i) = 0
参数：β i；h : κ -> ι；hh : Function.Injective h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFinsupp.zero_apply`：zero_apply (i : ι) : (0 : Π₀ i, β i) i = 0
· 使用定理 `DFinsupp.comapDomain_apply`：comapDomain_apply [forall i, Zero (β i)] (h 
: κ -> ι) (hh : Function.Injective h) (f : Π₀ i, β i) (k : κ) : comapDomain h hh
 f k = f (h k)
-/
theorem comapDomain_zero [∀ i, Zero (β i)] (h : κ → ι) (hh : Function.Injective h) :
    comapDomain h hh (0 : Π₀ i, β i) = 0 := by
  ext
  rw [zero_apply, comapDomain_apply, zero_apply]

@[simp]
/-
**DFinsupp.comapDomain_add** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：comapDomain_add [forall i, AddZeroClass (β i)] (h : κ -> ι) (hh : Function
.Injective h) (f g : Π₀ i, β i) : comapDomain h hh (f + g) = comapDomain h hh f 
+ comapDomain h hh g
参数：β i；h : κ -> ι；hh : Function.Injective h；f g : Π₀ i, β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFinsupp.add_apply`：add_apply [forall i, AddZeroClass (β i)] (g₁ g₂ : Π₀
 i, β i) (i : ι) : (g₁ + g₂) i = g₁ i + g₂ i
· 使用定理 `DFinsupp.comapDomain_apply`：comapDomain_apply [forall i, Zero (β i)] (h 
: κ -> ι) (hh : Function.Injective h) (f : Π₀ i, β i) (k : κ) : comapDomain h hh
 f k = f (h k)
-/
theorem comapDomain_add [∀ i, AddZeroClass (β i)] (h : κ → ι) (hh : Function.Injective h)
    (f g : Π₀ i, β i) : comapDomain h hh (f + g) = comapDomain h hh f + comapDomain h hh g := by
  ext
  rw [add_apply, comapDomain_apply, comapDomain_apply, comapDomain_apply, add_apply]

@[simp]
/-
**DFinsupp.comapDomain_single** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：comapDomain_single [DecidableEq ι] [DecidableEq κ] [forall i, Zero (β i)] 
(h : κ -> ι) (hh : Function.Injective h) (k : κ) (x : β (h k)) : comapDomain h h
h (single (h k) x) = single k x
参数：β i；h : κ -> ι；hh : Function.Injective h；k : κ；x : β (h k)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFinsupp.comapDomain_apply`：comapDomain_apply [forall i, Zero (β i)] (h 
: κ -> ι) (hh : Function.Injective h) (f : Π₀ i, β i) (k : κ) : comapDomain h hh
 f k = f (h k)
· 使用定理 `Decidable.eq_or_ne`：Decidable.eq_or_ne {α : Sort*} (x y : α) [Decidable 
(x = y)] : x = y ∨ x != y
· 使用定理 `DFinsupp.single_eq_same`：single_eq_same {i b} : (single i b : Π₀ i, β i)
 i = b
· 使用定理 `DFinsupp.single_eq_of_ne`：single_eq_of_ne {i i' b} (h : i' != i) : (sing
le i b : Π₀ i, β i) i' = 0
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
-/
theorem comapDomain_single [DecidableEq ι] [DecidableEq κ] [∀ i, Zero (β i)] (h : κ → ι)
    (hh : Function.Injective h) (k : κ) (x : β (h k)) :
    comapDomain h hh (single (h k) x) = single k x := by
  ext i
  rw [comapDomain_apply]
  obtain rfl | hik := Decidable.eq_or_ne i k
  · rw [single_eq_same, single_eq_same]
  · rw [single_eq_of_ne hik, single_eq_of_ne (hh.ne hik)]

/-- A computable version of `comapDomain` when an explicit left inverse is provided. -/
/-
**DFinsupp.comapDomain'** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp`。
形式化陈述：comapDomain' [forall i, Zero (β i)] (h : κ -> ι) {h' : ι -> κ} (hh' : Func
tion.LeftInverse h' h) (f : Π₀ i, β i) : Π₀ k, β (h k) where toFun x
参数：β i；h : κ -> ι；hh' : Function.LeftInverse h' h；f : Π₀ i, β i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A computable version of `comapDomain` when an explicit left inverse is provided.
-/
def comapDomain' [∀ i, Zero (β i)] (h : κ → ι) {h' : ι → κ} (hh' : Function.LeftInverse h' h)
    (f : Π₀ i, β i) : Π₀ k, β (h k) where
  toFun x := f (h x)
  support' :=
    f.support'.map fun s =>
      ⟨Multiset.map h' s.1, fun x =>
        (s.prop (h x)).imp_left fun hx => Multiset.mem_map.mpr ⟨_, hx, hh' _⟩⟩

@[simp, grind =]
/-
**DFinsupp.comapDomain'_apply** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：∀ {ι : Type u} {β : ι → Type v} {κ : Type u_1} [inst : (i : ι) → Zero (β i
)] (h : κ → ι) {h' : ι → κ}   (hh' : Function.LeftInverse h' h) (f : Π₀ (i : ι),
 β i) (k : κ), (DFinsupp.comapDomain' h hh' f) k = f (h k)
参数：i : ι；β i；h : κ → ι；hh' : Function.LeftInverse h' h；f : Π₀ (i : ι), β i；k : κ
；DFinsupp.comapDomain' h hh' f；h k。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comapDomain'_apply [∀ i, Zero (β i)] (h : κ → ι) {h' : ι → κ}
    (hh' : Function.LeftInverse h' h) (f : Π₀ i, β i) (k : κ) : comapDomain' h hh' f k = f (h k) :=
  rfl

@[simp]
/-
**DFinsupp.comapDomain'_zero** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：∀ {ι : Type u} {β : ι → Type v} {κ : Type u_1} [inst : (i : ι) → Zero (β i
)] (h : κ → ι) {h' : ι → κ}   (hh' : Function.LeftInverse h' h), DFinsupp.comapD
omain' h hh' 0 = 0
参数：i : ι；β i；h : κ → ι；hh' : Function.LeftInverse h' h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFinsupp.zero_apply`：zero_apply (i : ι) : (0 : Π₀ i, β i) i = 0
· 使用定理 `DFinsupp.comapDomain'_apply`：∀ {ι : Type u} {β : ι → Type v} {κ : Type u
_1} [inst : (i : ι) → Zero (β i)] (h : κ → ι) {h' : ι → κ}   (hh' : Function.Lef
tInverse h' h) (f…
-/
theorem comapDomain'_zero [∀ i, Zero (β i)] (h : κ → ι) {h' : ι → κ}
    (hh' : Function.LeftInverse h' h) : comapDomain' h hh' (0 : Π₀ i, β i) = 0 := by
  ext
  rw [zero_apply, comapDomain'_apply, zero_apply]

@[simp]
/-
**DFinsupp.comapDomain'_add** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：∀ {ι : Type u} {β : ι → Type v} {κ : Type u_1} [inst : (i : ι) → AddZeroCl
ass (β i)] (h : κ → ι) {h' : ι → κ}   (hh' : Function.LeftInverse h' h) (f g : Π
₀ (i : ι), β i),   DFinsupp.comapDomain' h hh' (f + g) = DFinsupp.comapDomain' h
 hh' f + DFinsupp.comapDomain' h hh' g
参数：i : ι；β i；h : κ → ι；hh' : Function.LeftInverse h' h；f g : Π₀ (i : ι), β i；f +
 g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFinsupp.add_apply`：add_apply [forall i, AddZeroClass (β i)] (g₁ g₂ : Π₀
 i, β i) (i : ι) : (g₁ + g₂) i = g₁ i + g₂ i
· 使用定理 `DFinsupp.comapDomain'_apply`：∀ {ι : Type u} {β : ι → Type v} {κ : Type u
_1} [inst : (i : ι) → Zero (β i)] (h : κ → ι) {h' : ι → κ}   (hh' : Function.Lef
tInverse h' h) (f…
-/
theorem comapDomain'_add [∀ i, AddZeroClass (β i)] (h : κ → ι) {h' : ι → κ}
    (hh' : Function.LeftInverse h' h) (f g : Π₀ i, β i) :
    comapDomain' h hh' (f + g) = comapDomain' h hh' f + comapDomain' h hh' g := by
  ext
  rw [add_apply, comapDomain'_apply, comapDomain'_apply, comapDomain'_apply, add_apply]

@[simp]
/-
**DFinsupp.comapDomain'_single** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：∀ {ι : Type u} {β : ι → Type v} {κ : Type u_1} [inst : DecidableEq ι] [ins
t_1 : DecidableEq κ]   [inst_2 : (i : ι) → Zero (β i)] (h : κ → ι) {h' : ι → κ} 
(hh' : Function.LeftInverse h' h) (k : κ) (x : β (h k)),   (DFinsupp.comapDomain
' h hh' fun₀ | h k => x) = fun₀ | k => x
参数：i : ι；β i；h : κ → ι；hh' : Function.LeftInverse h' h；k : κ；x : β (h k)；DFinsup
p.comapDomain' h hh' fun₀ | h k => x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comapDomain'_single [DecidableEq ι] [DecidableEq κ] [∀ i, Zero (β i)] (h : κ → ι)
    {h' : ι → κ} (hh' : Function.LeftInverse h' h) (k : κ) (x : β (h k)) :
    comapDomain' h hh' (single (h k) x) = single k x := by
  grind

set_option backward.isDefEq.respectTransparency false in
/-- Reindexing terms of a dfinsupp.

This is the dfinsupp version of `Equiv.piCongrLeft'`. -/
@[simps apply]
/-
**DFinsupp.equivCongrLeft** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp`。
形式化陈述：equivCongrLeft [forall i, Zero (β i)] (h : ι ≃ κ) : (Π₀ i, β i) ≃ Π₀ k, β 
(h.symm k) where toFun
参数：β i；h : ι ≃ κ。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun

--- 原说明 ---
Reindexing terms of a dfinsupp.

This is the dfinsupp version of `Equiv.piCongrLeft'`.
-/
def equivCongrLeft [∀ i, Zero (β i)] (h : ι ≃ κ) : (Π₀ i, β i) ≃ Π₀ k, β (h.symm k) where
  toFun := comapDomain' h.symm h.right_inv
  invFun f :=
    mapRange (fun i => Equiv.cast <| congr_arg β <| h.symm_apply_apply i)
      (fun i => (Equiv.cast_eq_iff_heq _).mpr <| by rw [Equiv.symm_apply_apply])
      (@comapDomain' _ _ _ _ h _ h.left_inv f)
  left_inv f := by
    ext i
    rw [mapRange_apply, comapDomain'_apply, comapDomain'_apply, Equiv.cast_eq_iff_heq,
      h.symm_apply_apply]
  right_inv f := by
    ext k
    rw [comapDomain'_apply, mapRange_apply, comapDomain'_apply, Equiv.cast_eq_iff_heq,
      h.apply_symm_apply]

variable {α : Option ι → Type v}

/-- Adds a term to a dfinsupp, making a dfinsupp indexed by an `Option`.

This is the dfinsupp version of `Option.rec`. -/
/-
**DFinsupp.extendWith** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp`。
形式化陈述：extendWith [forall i, Zero (α i)] (a : α none) (f : Π₀ i, α (some i)) : Π₀
 i, α i where toFun
参数：α i；a : α none；f : Π₀ i, α (some i)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Adds a term to a dfinsupp, making a dfinsupp indexed by an `Option`.

This is the dfinsupp version of `Option.rec`.
-/
def extendWith [∀ i, Zero (α i)] (a : α none) (f : Π₀ i, α (some i)) : Π₀ i, α i where
  toFun := fun i ↦ match i with | none => a | some _ => f _
  support' :=
    f.support'.map fun s =>
      ⟨none ::ₘ Multiset.map some s.1, fun i =>
        Option.rec (Or.inl <| Multiset.mem_cons_self _ _)
          (fun i =>
            (s.prop i).imp_left fun h => Multiset.mem_cons_of_mem <| Multiset.mem_map_of_mem _ h)
          i⟩

@[simp]
/-
**DFinsupp.extendWith_none** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：extendWith_none [forall i, Zero (α i)] (f : Π₀ i, α (some i)) (a : α none)
 : f.extendWith a none = a
参数：α i；f : Π₀ i, α (some i)；a : α none。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem extendWith_none [∀ i, Zero (α i)] (f : Π₀ i, α (some i)) (a : α none) :
    f.extendWith a none = a :=
  rfl

@[simp]
/-
**DFinsupp.extendWith_some** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：extendWith_some [forall i, Zero (α i)] (f : Π₀ i, α (some i)) (a : α none)
 (i : ι) : f.extendWith a (some i) = f i
参数：α i；f : Π₀ i, α (some i)；a : α none；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem extendWith_some [∀ i, Zero (α i)] (f : Π₀ i, α (some i)) (a : α none) (i : ι) :
    f.extendWith a (some i) = f i :=
  rfl

@[simp]
/-
**DFinsupp.extendWith_single_zero** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：extendWith_single_zero [DecidableEq ι] [forall i, Zero (α i)] (i : ι) (x :
 α (some i)) : (single i x).extendWith 0 = single (some i) x
参数：α i；i : ι；x : α (some i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFinsupp.extendWith_none`：extendWith_none [forall i, Zero (α i)] (f : Π₀
 i, α (some i)) (a : α none) : f.extendWith a none = a
· 使用定理 `DFinsupp.single_eq_of_ne`：single_eq_of_ne {i i' b} (h : i' != i) : (sing
le i b : Π₀ i, β i) i' = 0
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Option.some_ne_none`：∀ {α : Type u_1} (x : α), some x ≠ none
· 使用定理 `DFinsupp.extendWith_some`：extendWith_some [forall i, Zero (α i)] (f : Π₀
 i, α (some i)) (a : α none) (i : ι) : f.extendWith a (some i) = f i
· 使用定理 `Decidable.eq_or_ne`：Decidable.eq_or_ne {α : Sort*} (x y : α) [Decidable 
(x = y)] : x = y ∨ x != y
· 使用定理 `DFinsupp.single_eq_same`：single_eq_same {i b} : (single i b : Π₀ i, β i)
 i = b
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `Option.some_injective`：some_injective (α : Type*) : Function.Injective (
@some α)
-/
theorem extendWith_single_zero [DecidableEq ι] [∀ i, Zero (α i)] (i : ι) (x : α (some i)) :
    (single i x).extendWith 0 = single (some i) x := by
  ext (_ | j)
  · rw [extendWith_none, single_eq_of_ne (Option.some_ne_none _).symm]
  · rw [extendWith_some]
    obtain rfl | hij := Decidable.eq_or_ne j i
    · rw [single_eq_same, single_eq_same]
    · rw [single_eq_of_ne hij, single_eq_of_ne ((Option.some_injective _).ne hij)]

@[simp]
/-
**DFinsupp.extendWith_zero** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：extendWith_zero [DecidableEq ι] [forall i, Zero (α i)] (x : α none) : (0 :
 Π₀ i, α (some i)).extendWith x = single none x
参数：α i；x : α none。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFinsupp.extendWith_none`：extendWith_none [forall i, Zero (α i)] (f : Π₀
 i, α (some i)) (a : α none) : f.extendWith a none = a
· 使用定理 `DFinsupp.single_eq_same`：single_eq_same {i b} : (single i b : Π₀ i, β i)
 i = b
· 使用定理 `DFinsupp.extendWith_some`：extendWith_some [forall i, Zero (α i)] (f : Π₀
 i, α (some i)) (a : α none) (i : ι) : f.extendWith a (some i) = f i
· 使用定理 `DFinsupp.single_eq_of_ne`：single_eq_of_ne {i i' b} (h : i' != i) : (sing
le i b : Π₀ i, β i) i' = 0
· 使用定理 `Option.some_ne_none`：∀ {α : Type u_1} (x : α), some x ≠ none
· 使用定理 `DFinsupp.zero_apply`：zero_apply (i : ι) : (0 : Π₀ i, β i) i = 0
-/
theorem extendWith_zero [DecidableEq ι] [∀ i, Zero (α i)] (x : α none) :
    (0 : Π₀ i, α (some i)).extendWith x = single none x := by
  ext (_ | j)
  · rw [extendWith_none, single_eq_same]
  · rw [extendWith_some, single_eq_of_ne (Option.some_ne_none _), zero_apply]

/-- Bijection obtained by separating the term of index `none` of a dfinsupp over `Option ι`.

This is the dfinsupp version of `Equiv.piOptionEquivProd`. -/
@[simps]
/-
**DFinsupp.equivProdDFinsupp** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp`。
形式化陈述：equivProdDFinsupp [forall i, Zero (α i)] : (Π₀ i, α i) ≃ α none × Π₀ i, α 
(some i) where toFun f
参数：α i。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Option.some_injective`：some_injective (α : Type*) : Function.Injective (
@some α)

--- 原说明 ---
Bijection obtained by separating the term of index `none` of a dfinsupp over `Op
tion ι`.

This is the dfinsupp version of `Equiv.piOptionEquivProd`.
-/
noncomputable def equivProdDFinsupp [∀ i, Zero (α i)] :
    (Π₀ i, α i) ≃ α none × Π₀ i, α (some i) where
  toFun f := (f none, comapDomain some (Option.some_injective _) f)
  invFun f := f.2.extendWith f.1
  left_inv f := by
    ext i; obtain - | i := i
    · rw [extendWith_none]
    · rw [extendWith_some, comapDomain_apply]
  right_inv x := by
    dsimp only
    ext
    · exact extendWith_none x.snd _
    · rw [comapDomain_apply, extendWith_some]
/-
**DFinsupp.equivProdDFinsupp_add** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：equivProdDFinsupp_add [forall i, AddZeroClass (α i)] (f g : Π₀ i, α i) : e
quivProdDFinsupp (f + g) = equivProdDFinsupp f + equivProdDFinsupp g
参数：α i；f g : Π₀ i, α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `DFinsupp.add_apply`：add_apply [forall i, AddZeroClass (β i)] (g₁ g₂ : Π₀
 i, β i) (i : ι) : (g₁ + g₂) i = g₁ i + g₂ i
· 使用定理 `DFinsupp.comapDomain_add`：comapDomain_add [forall i, AddZeroClass (β i)]
 (h : κ -> ι) (hh : Function.Injective h) (f g : Π₀ i, β i) : comapDomain h hh (
f + g) = comap…
· 使用定理 `Option.some_injective`：some_injective (α : Type*) : Function.Injective (
@some α)
-/
theorem equivProdDFinsupp_add [∀ i, AddZeroClass (α i)] (f g : Π₀ i, α i) :
    equivProdDFinsupp (f + g) = equivProdDFinsupp f + equivProdDFinsupp g :=
  Prod.ext (add_apply _ _ _) (comapDomain_add _ (Option.some_injective _) _ _)

end Equiv

/-! ### Bundled versions of `DFinsupp.mapRange`

The names should match the equivalent bundled `Finsupp.mapRange` definitions.
-/


section MapRange

variable [∀ i, AddZeroClass (β i)] [∀ i, AddZeroClass (β₁ i)] [∀ i, AddZeroClass (β₂ i)]

/-
**DFinsupp.mapRange_add** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：mapRange_add (f : forall i, β₁ i -> β₂ i) (hf : forall i, f i 0 = 0) (hf' 
: forall i x y, f i (x + y) = f i x + f i y) (g₁ g₂ : Π₀ i, β₁ i) : mapRange f h
f (g₁ + g₂) = mapRange f hf g₁ + mapRange f hf g₂
参数：f : forall i, β₁ i -> β₂ i；hf : forall i, f i 0 = 0；hf' : forall i x y, f i (
x + y) = f i x + f i y；g₁ g₂ : Π₀ i, β₁ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mapRange_add (f : ∀ i, β₁ i → β₂ i) (hf : ∀ i, f i 0 = 0)
    (hf' : ∀ i x y, f i (x + y) = f i x + f i y) (g₁ g₂ : Π₀ i, β₁ i) :
    mapRange f hf (g₁ + g₂) = mapRange f hf g₁ + mapRange f hf g₂ := by
  ext
  simp only [mapRange_apply f, coe_add, Pi.add_apply, hf']

/-- `DFinsupp.mapRange` as an `AddMonoidHom`. -/
@[simps apply]
/-
**DFinsupp.mapRange.addMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp.mapRange`。
形式化陈述：{ι : Type u} →   {β₁ : ι → Type v₁} →     {β₂ : ι → Type v₂} →       [inst
 : (i : ι) → AddZeroClass (β₁ i)] →         [inst_1 : (i : ι) → AddZeroClass (β₂
 i)] → ((i : ι) → β₁ i →+ β₂ i) → (Π₀ (i : ι), β₁ i) →+ Π₀ (i : ι), β₂ i
参数：i : ι；β₁ i；i : ι；β₂ i；(i : ι) → β₁ i →+ β₂ i；Π₀ (i : ι), β₁ i；i : ι。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`DFinsupp.mapRange` as an `AddMonoidHom`.
-/
def mapRange.addMonoidHom (f : ∀ i, β₁ i →+ β₂ i) : (Π₀ i, β₁ i) →+ Π₀ i, β₂ i where
  toFun := mapRange (fun i x => f i x) fun i => (f i).map_zero
  map_zero' := mapRange_zero _ _
  map_add' := mapRange_add _ (fun i => (f i).map_zero) fun i => (f i).map_add

@[simp]
/-
**DFinsupp.mapRange.addMonoidHom_id** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp.mapRange
`。
形式化陈述：∀ {ι : Type u} {β₂ : ι → Type v₂} [inst : (i : ι) → AddZeroClass (β₂ i)], 
  (DFinsupp.mapRange.addMonoidHom fun i => AddMonoidHom.id (β₂ i)) = AddMonoidHo
m.id (Π₀ (i : ι), β₂ i)
参数：i : ι；β₂ i；DFinsupp.mapRange.addMonoidHom fun i => AddMonoidHom.id (β₂ i)；Π₀ 
(i : ι), β₂ i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g
· 使用定理 `DFinsupp.mapRange_id`：mapRange_id (h : forall i, id (0 : β₁ i) = 0
-/
theorem mapRange.addMonoidHom_id :
    (mapRange.addMonoidHom fun i => AddMonoidHom.id (β₂ i)) = AddMonoidHom.id _ :=
  AddMonoidHom.ext mapRange_id
/-
**DFinsupp.mapRange.addMonoidHom_comp** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp.mapRan
ge`。
形式化陈述：∀ {ι : Type u} {β : ι → Type v} {β₁ : ι → Type v₁} {β₂ : ι → Type v₂} [ins
t : (i : ι) → AddZeroClass (β i)]   [inst_1 : (i : ι) → AddZeroClass (β₁ i)] [in
st_2 : (i : ι) → AddZeroClass (β₂ i)] (f : (i : ι) → β₁ i →+ β₂ i)   (f₂ : (i : 
ι) → β i →+ β₁ i),   (DFinsupp.mapRange.addMonoidHom fun i => (f i).comp (f₂ i))
 =     (DFinsupp.mapRange.addMonoidHom f).comp (DFinsupp.mapRange.addMonoidHom f
₂)
参数：i : ι；β i；i : ι；β₁ i；i : ι；β₂ i；f : (i : ι) → β₁ i →+ β₂ i；f₂ : (i : ι) → β i
 →+ β₁ i；DFinsupp.mapRange.addMonoidHom fun i => (f i).comp (f₂ i)；DFinsupp.mapR
ange.addMonoidHom f；DFinsupp.mapRange.addMonoidHom f₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `DFinsupp.mapRange.addMonoidHom_apply`：∀ {ι : Type u} {β₁ : ι → Type v₁} 
{β₂ : ι → Type v₂} [inst : (i : ι) → AddZeroClass (β₁ i)]   [inst_1 : (i : ι) → 
AddZeroClass (β₂ i)] (f : …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mapRange.addMonoidHom_comp (f : ∀ i, β₁ i →+ β₂ i) (f₂ : ∀ i, β i →+ β₁ i) :
    (mapRange.addMonoidHom fun i => (f i).comp (f₂ i)) =
      (mapRange.addMonoidHom f).comp (mapRange.addMonoidHom f₂) := by
  ext
  simp

/-- `DFinsupp.mapRange.addMonoidHom` as an `AddEquiv`. -/
@[simps apply]
/-
**DFinsupp.mapRange.addEquiv** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp.mapRange`。
形式化陈述：{ι : Type u} →   {β₁ : ι → Type v₁} →     {β₂ : ι → Type v₂} →       [inst
 : (i : ι) → AddZeroClass (β₁ i)] →         [inst_1 : (i : ι) → AddZeroClass (β₂
 i)] → ((i : ι) → β₁ i ≃+ β₂ i) → (Π₀ (i : ι), β₁ i) ≃+ Π₀ (i : ι), β₂ i
参数：i : ι；β₁ i；i : ι；β₂ i；(i : ι) → β₁ i ≃+ β₂ i；Π₀ (i : ι), β₁ i；i : ι。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`DFinsupp.mapRange.addMonoidHom` as an `AddEquiv`.
-/
def mapRange.addEquiv (e : ∀ i, β₁ i ≃+ β₂ i) : (Π₀ i, β₁ i) ≃+ Π₀ i, β₂ i :=
  { mapRange.addMonoidHom fun i =>
      (e i).toAddMonoidHom with
    toFun := mapRange (fun i x => e i x) fun i => (e i).map_zero
    invFun := mapRange (fun i x => (e i).symm x) fun i => (e i).symm.map_zero
    left_inv := fun x => by
      rw [← mapRange_comp] <;>
        · simp_rw [AddEquiv.symm_comp_self]
          simp
    right_inv := fun x => by
      rw [← mapRange_comp] <;>
        · simp_rw [AddEquiv.self_comp_symm]
          simp }

@[simp]
/-
**DFinsupp.mapRange.addEquiv_refl** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp.mapRange`。
形式化陈述：∀ {ι : Type u} {β₁ : ι → Type v₁} [inst : (i : ι) → AddZeroClass (β₁ i)], 
  (DFinsupp.mapRange.addEquiv fun i => AddEquiv.refl (β₁ i)) = AddEquiv.refl (Π₀
 (i : ι), β₁ i)
参数：i : ι；β₁ i；DFinsupp.mapRange.addEquiv fun i => AddEquiv.refl (β₁ i)；Π₀ (i : ι
), β₁ i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddEquiv.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [inst_1 : A
dd N] {f g : M ≃+ N}, (∀ (x : M), f x = g x) → f = g
· 使用定理 `DFinsupp.mapRange_id`：mapRange_id (h : forall i, id (0 : β₁ i) = 0
-/
theorem mapRange.addEquiv_refl :
    (mapRange.addEquiv fun i => AddEquiv.refl (β₁ i)) = AddEquiv.refl _ :=
  AddEquiv.ext mapRange_id
/-
**DFinsupp.mapRange.addEquiv_trans** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp.mapRange`
。
形式化陈述：∀ {ι : Type u} {β : ι → Type v} {β₁ : ι → Type v₁} {β₂ : ι → Type v₂} [ins
t : (i : ι) → AddZeroClass (β i)]   [inst_1 : (i : ι) → AddZeroClass (β₁ i)] [in
st_2 : (i : ι) → AddZeroClass (β₂ i)] (f : (i : ι) → β i ≃+ β₁ i)   (f₂ : (i : ι
) → β₁ i ≃+ β₂ i),   (DFinsupp.mapRange.addEquiv fun i => (f i).trans (f₂ i)) = 
    (DFinsupp.mapRange.addEquiv f).trans (DFinsupp.mapRange.addEquiv f₂)
参数：i : ι；β i；i : ι；β₁ i；i : ι；β₂ i；f : (i : ι) → β i ≃+ β₁ i；f₂ : (i : ι) → β₁ i
 ≃+ β₂ i；DFinsupp.mapRange.addEquiv fun i => (f i).trans (f₂ i)；DFinsupp.mapRang
e.addEquiv f；DFinsupp.mapRange.addEquiv f₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddEquiv.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [inst_1 : A
dd N] {f g : M ≃+ N}, (∀ (x : M), f x = g x) → f = g
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `DFinsupp.mapRange.addEquiv_apply`：∀ {ι : Type u} {β₁ : ι → Type v₁} {β₂ 
: ι → Type v₂} [inst : (i : ι) → AddZeroClass (β₁ i)]   [inst_1 : (i : ι) → AddZ
eroClass (β₂ i)] (e : …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mapRange.addEquiv_trans (f : ∀ i, β i ≃+ β₁ i) (f₂ : ∀ i, β₁ i ≃+ β₂ i) :
    (mapRange.addEquiv fun i => (f i).trans (f₂ i)) =
      (mapRange.addEquiv f).trans (mapRange.addEquiv f₂) := by
  ext
  simp

@[simp]
/-
**DFinsupp.mapRange.addEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp.mapRange`。
形式化陈述：∀ {ι : Type u} {β₁ : ι → Type v₁} {β₂ : ι → Type v₂} [inst : (i : ι) → Add
ZeroClass (β₁ i)]   [inst_1 : (i : ι) → AddZeroClass (β₂ i)] (e : (i : ι) → β₁ i
 ≃+ β₂ i),   (DFinsupp.mapRange.addEquiv e).symm = DFinsupp.mapRange.addEquiv fu
n i => (e i).symm
参数：i : ι；β₁ i；i : ι；β₂ i；e : (i : ι) → β₁ i ≃+ β₂ i；DFinsupp.mapRange.addEquiv e
；e i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapRange.addEquiv_symm (e : ∀ i, β₁ i ≃+ β₂ i) :
    (mapRange.addEquiv e).symm = mapRange.addEquiv fun i => (e i).symm :=
  rfl

end MapRange

end DFinsupp

