/-
Copyright (c) 2024 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.SetTheory.Ordinal.FixedPoint

/-!
# Veblen hierarchy

We define the two-arguments Veblen function, which satisfies `veblen 0 a = ω ^ a` and that for
`o ≠ 0`, `veblen o` enumerates the common fixed points of `veblen o'` for `o' < o`.

We use this to define two important functions on ordinals: the epsilon function `ε_ o = veblen 1 o`,
and the gamma function `Γ_ o` enumerating the fixed points of `veblen · 0`.

## Main definitions

* `veblenWith`: The Veblen hierarchy with a specified initial function.
* `veblen`: The Veblen hierarchy starting with `ω ^ ·`.

## Notation

The following notation is scoped to the `Ordinal` namespace.

- `ε_ o` is notation for `veblen 1 o`. `ε₀` is notation for `ε_ 0`.
- `Γ_ o` is notation for `gamma o`. `Γ₀` is notation for `Γ_ 0`.

## TODO

- Prove that `ε₀` and `Γ₀` are countable.
- Prove that the ordinals principal under `veblen` are the gamma ordinals (and 0).

## References

* [Larry W. Miller, Normal functions and constructive ordinal notations][Miller_1976]
-/

@[expose] public section

noncomputable section

open Order Set

universe u

namespace Ordinal

variable {f : Ordinal.{u} → Ordinal.{u}} {o o₁ o₂ a b x : Ordinal.{u}}

/-! ### Veblen function with a given starting function -/

section veblenWith

/-- `veblenWith f o` is the `o`-th function in the Veblen hierarchy starting with `f`. This is
defined so that

- `veblenWith f 0 = f`.
- `veblenWith f o` for `o ≠ 0` enumerates the common fixed points of `veblenWith f o'` over all
  `o' < o`.
-/
@[pp_nodot]
/-
**Ordinal.veblenWith** 是 Mathlib 中的一个定义，位于命名空间 `Ordinal`。
形式化陈述：veblenWith (f : Ordinal.{u} -> Ordinal.{u}) (o : Ordinal.{u}) : Ordinal.{u
} -> Ordinal.{u}
参数：f : Ordinal.{u} -> Ordinal.{u}；o : Ordinal.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`veblenWith f o` is the `o`-th function in the Veblen hierarchy starting with `f
`. This is
defined so that

- `veblenWith f 0 = f`.
- `veblenWith f o` for `o ≠ 0` enumerates the common fixed points of `veblenWith
 f o'` over all
  `o' < o`.
-/
def veblenWith (f : Ordinal.{u} → Ordinal.{u}) (o : Ordinal.{u}) : Ordinal.{u} → Ordinal.{u} :=
  if o = 0 then f else derivFamily fun (⟨x, _⟩ : Iio o) ↦ veblenWith f x
termination_by o

@[simp]
/-
**Ordinal.veblenWith_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：veblenWith_zero (f : Ordinal -> Ordinal) : veblenWith f 0 = f
参数：f : Ordinal -> Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.veblenWith.eq_1`：∀ (f : Ordinal.{u} → Ordinal.{u}) (o : Ordinal.
{u}),   Ordinal.veblenWith f o =     if o = 0 then f     else       Ordinal.deri
vFamily fun x…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem veblenWith_zero (f : Ordinal → Ordinal) : veblenWith f 0 = f := by
  rw [veblenWith, if_pos rfl]
/-
**Ordinal.veblenWith_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：veblenWith_of_ne_zero (f : Ordinal -> Ordinal) (h : o != 0) : veblenWith f
 o = derivFamily fun x : Iio o => veblenWith f x.1
参数：f : Ordinal -> Ordinal；h : o != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.veblenWith.eq_1`：∀ (f : Ordinal.{u} → Ordinal.{u}) (o : Ordinal.
{u}),   Ordinal.veblenWith f o =     if o = 0 then f     else       Ordinal.deri
vFamily fun x…
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem veblenWith_of_ne_zero (f : Ordinal → Ordinal) (h : o ≠ 0) :
    veblenWith f o = derivFamily fun x : Iio o ↦ veblenWith f x.1 := by
  rw [veblenWith, if_neg h]

/-- `veblenWith f o` is always normal for `o ≠ 0`. See `isNormal_veblenWith` for a version which
assumes `IsNormal f`. -/
/-
**Ordinal.isNormal_veblenWith'** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isNormal_veblenWith' (f : Ordinal -> Ordinal) (h : o != 0) : IsNormal (veb
lenWith f o)
参数：f : Ordinal -> Ordinal；h : o != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.veblenWith_of_ne_zero`：veblenWith_of_ne_zero (f : Ordinal -> Ord
inal) (h : o != 0) : veblenWith f o = derivFamily fun x : Iio o => veblenWith f 
x.1
· 使用定理 `Ordinal.isNormal_derivFamily`：isNormal_derivFamily [Small.{u} ι] (f : ι 
-> Ordinal.{u} -> Ordinal.{u}) : IsNormal (derivFamily f)

--- 原说明 ---
`veblenWith f o` is always normal for `o ≠ 0`. See `isNormal_veblenWith` for a v
ersion which
assumes `IsNormal f`.
-/
theorem isNormal_veblenWith' (f : Ordinal → Ordinal) (h : o ≠ 0) : IsNormal (veblenWith f o) := by
  rw [veblenWith_of_ne_zero f h]
  exact isNormal_derivFamily _

variable (hf : IsNormal f)
include hf

/-- `veblenWith f o` is always normal whenever `f` is. See `isNormal_veblenWith'` for a version
which does not assume `IsNormal f`. -/
/-
**Ordinal.isNormal_veblenWith** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isNormal_veblenWith (o : Ordinal) : IsNormal (veblenWith f o)
参数：o : Ordinal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.veblenWith_zero`：veblenWith_zero (f : Ordinal -> Ordinal) : vebl
enWith f 0 = f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.isNormal_veblenWith'`：isNormal_veblenWith' (f : Ordinal -> Ordin
al) (h : o != 0) : IsNormal (veblenWith f o)

--- 原说明 ---
`veblenWith f o` is always normal whenever `f` is. See `isNormal_veblenWith'` fo
r a version
which does not assume `IsNormal f`.
-/
theorem isNormal_veblenWith (o : Ordinal) : IsNormal (veblenWith f o) := by
  obtain rfl | h := eq_or_ne o 0
  · rwa [veblenWith_zero]
  · exact isNormal_veblenWith' f h
/-
**Ordinal.mem_range_veblenWith** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：mem_range_veblenWith (h : o != 0) : a in range (veblenWith f o) ↔ forall b
 < o, veblenWith f b a = a
参数：h : o != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.veblenWith_of_ne_zero`：veblenWith_of_ne_zero (f : Ordinal -> Ord
inal) (h : o != 0) : veblenWith f o = derivFamily fun x : Iio o => veblenWith f 
x.1
· 使用定理 `Ordinal.mem_range_derivFamily`：mem_range_derivFamily [Small.{u} ι] (H : 
forall i, IsNormal (f i)) {a} : a in Set.range (derivFamily f) ↔ forall i, f i a
 = a
· 使用定理 `Ordinal.isNormal_veblenWith`：isNormal_veblenWith (o : Ordinal) : IsNorma
l (veblenWith f o)
· 使用定理 `Subtype.forall`：∀ {α : Sort u} {p : α → Prop} {q : { a // p a } → Prop},
 (∀ (x : { a // p a }), q x) ↔ ∀ (a : α) (b : p a), q ⟨a, b⟩
-/
theorem mem_range_veblenWith (h : o ≠ 0) :
    a ∈ range (veblenWith f o) ↔ ∀ b < o, veblenWith f b a = a := by
  rw [veblenWith_of_ne_zero f h, mem_range_derivFamily (fun _ ↦ isNormal_veblenWith hf _)]
  exact Subtype.forall
/-
**Ordinal.veblenWith_veblenWith_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：veblenWith_veblenWith_of_lt (h : o₁ < o₂) (a : Ordinal) : veblenWith f o₁ 
(veblenWith f o₂ a) = veblenWith f o₂ a
参数：h : o₁ < o₂；a : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ordinal.mem_range_veblenWith`：mem_range_veblenWith (h : o != 0) : a in r
ange (veblenWith f o) ↔ forall b < o, veblenWith f b a = a
· 使用定理 `LT.lt.ne_bot`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α] {
a b : α}, b < a → a ≠ ⊥
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem veblenWith_veblenWith_of_lt (h : o₁ < o₂) (a : Ordinal) :
    veblenWith f o₁ (veblenWith f o₂ a) = veblenWith f o₂ a := by
  apply (mem_range_veblenWith hf h.ne_bot).1 _ _ h
  simp
/-
**Ordinal.veblenWith_eq_self_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：veblenWith_eq_self_of_le (h : o₁ <= o₂) (h' : veblenWith f o₂ a = a) : veb
lenWith f o₁ a = a
参数：h : o₁ <= o₂；h' : veblenWith f o₂ a = a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.veblenWith_veblenWith_of_lt`：veblenWith_veblenWith_of_lt (h : o₁
 < o₂) (a : Ordinal) : veblenWith f o₁ (veblenWith f o₂ a) = veblenWith f o₂ a
-/
theorem veblenWith_eq_self_of_le (h : o₁ ≤ o₂) (h' : veblenWith f o₂ a = a) :
    veblenWith f o₁ a = a := by
  obtain rfl | h := h.eq_or_lt
  · assumption
  · rw [← h', veblenWith_veblenWith_of_lt hf h]
/-
**Ordinal.veblenWith_mem_range** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：veblenWith_mem_range : veblenWith f o a in range f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_zero_or_pos`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero 
α] [IsBotZeroClass α] (a : α), a = 0 ∨ 0 < a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Ordinal.veblenWith_zero`：veblenWith_zero (f : Ordinal -> Ordinal) : vebl
enWith f 0 = f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.veblenWith_veblenWith_of_lt`：veblenWith_veblenWith_of_lt (h : o₁
 < o₂) (a : Ordinal) : veblenWith f o₁ (veblenWith f o₂ a) = veblenWith f o₂ a
-/
theorem veblenWith_mem_range : veblenWith f o a ∈ range f := by
  obtain rfl | h := eq_zero_or_pos o
  · simp
  · rw [← veblenWith_veblenWith_of_lt hf h]
    simp
/-
**Ordinal.veblenWith_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：veblenWith_add_one (o : Ordinal) : veblenWith f (o + 1) = deriv (veblenWit
h f o)
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.deriv_eq_enumOrd`：deriv_eq_enumOrd (H : IsNormal f) : deriv f = 
enumOrd (Function.fixedPoints f)
· 使用定理 `Ordinal.isNormal_veblenWith`：isNormal_veblenWith (o : Ordinal) : IsNorma
l (veblenWith f o)
· 使用定理 `Ordinal.veblenWith_of_ne_zero`：veblenWith_of_ne_zero (f : Ordinal -> Ord
inal) (h : o != 0) : veblenWith f o = derivFamily fun x : Iio o => veblenWith f 
x.1
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `add_pos_of_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Pre
order α] [IsBotZeroClass α] [AddRightMono α] {b : α},   0 < b → ∀ (a : α), 0 < a
 + b
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
· 使用定理 `Ordinal.derivFamily_eq_enumOrd`：derivFamily_eq_enumOrd [Small.{u} ι] (H 
: forall i, IsNormal (f i)) : derivFamily f = enumOrd (⋂ i, Function.fixedPoints
 (f i))
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Set.mem_iInter`：mem_iInter {x : α} {s : ι -> Set α} : (x in ⋂ i, s i) ↔ 
forall i, x in s i
· 使用定理 `Order.lt_succ`：lt_succ (a : α) : a < succ a
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Order.lt_succ_iff_eq_or_lt`：lt_succ_iff_eq_or_lt : a < succ b ↔ a = b ∨ 
a < b
· 使用定理 `Function.mem_fixedPoints_iff`：mem_fixedPoints_iff {α : Type*} {f : α -> 
α} {x : α} : x in fixedPoints f ↔ f x = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.veblenWith_veblenWith_of_lt`：veblenWith_veblenWith_of_lt (h : o₁
 < o₂) (a : Ordinal) : veblenWith f o₁ (veblenWith f o₂ a) = veblenWith f o₂ a
-/
theorem veblenWith_add_one (o : Ordinal) : veblenWith f (o + 1) = deriv (veblenWith f o) := by
  rw [deriv_eq_enumOrd (isNormal_veblenWith hf o),
    veblenWith_of_ne_zero f (add_pos_of_right zero_lt_one _).ne', derivFamily_eq_enumOrd]
  · apply congr_arg
    ext a
    rw [mem_iInter]
    use fun ha ↦ ha ⟨o, lt_succ o⟩
    rintro (ha : _ = _) ⟨b, hb : b < _⟩
    obtain rfl | hb := lt_succ_iff_eq_or_lt.1 hb
    · rw [Function.mem_fixedPoints_iff, ha]
    · rw [← ha]
      exact veblenWith_veblenWith_of_lt hf hb _
  · exact fun o ↦ isNormal_veblenWith hf o.1

@[simp]
/-
**Ordinal.veblenWith_one** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：veblenWith_one : veblenWith f 1 = deriv f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Ordinal.veblenWith_zero`：veblenWith_zero (f : Ordinal -> Ordinal) : vebl
enWith f 0 = f
· 使用定理 `Ordinal.veblenWith_add_one`：veblenWith_add_one (o : Ordinal) : veblenWit
h f (o + 1) = deriv (veblenWith f o)
-/
theorem veblenWith_one : veblenWith f 1 = deriv f := by
  simpa using veblenWith_add_one hf 0

@[deprecated veblenWith_add_one (since := "2026-02-26")]
/-
**Ordinal.veblenWith_succ** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：veblenWith_succ (o : Ordinal) : veblenWith f (succ o) = deriv (veblenWith 
f o)
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.veblenWith_add_one`：veblenWith_add_one (o : Ordinal) : veblenWit
h f (o + 1) = deriv (veblenWith f o)
-/
theorem veblenWith_succ (o : Ordinal) : veblenWith f (succ o) = deriv (veblenWith f o) :=
  veblenWith_add_one hf o
/-
**Ordinal.veblenWith_right_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：veblenWith_right_strictMono (o : Ordinal) : StrictMono (veblenWith f o)
参数：o : Ordinal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsNormal.strictMono`：∀ {α : Type u_1} {β : Type u_2} [inst : Linea
rOrder α] [inst_1 : LinearOrder β] {f : α → β},   Order.IsNormal f → StrictMono 
f
· 使用定理 `Ordinal.isNormal_veblenWith`：isNormal_veblenWith (o : Ordinal) : IsNorma
l (veblenWith f o)
-/
theorem veblenWith_right_strictMono (o : Ordinal) : StrictMono (veblenWith f o) :=
  (isNormal_veblenWith hf o).strictMono

@[simp]
/-
**Ordinal.veblenWith_lt_veblenWith_iff_right** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`
。
形式化陈述：veblenWith_lt_veblenWith_iff_right : veblenWith f o a < veblenWith f o b ↔
 a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用定理 `Ordinal.veblenWith_right_strictMono`：veblenWith_right_strictMono (o : Or
dinal) : StrictMono (veblenWith f o)
-/
theorem veblenWith_lt_veblenWith_iff_right : veblenWith f o a < veblenWith f o b ↔ a < b :=
  (veblenWith_right_strictMono hf o).lt_iff_lt

@[simp]
/-
**Ordinal.veblenWith_le_veblenWith_iff_right** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`
。
形式化陈述：veblenWith_le_veblenWith_iff_right : veblenWith f o a <= veblenWith f o b 
↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用定理 `Ordinal.veblenWith_right_strictMono`：veblenWith_right_strictMono (o : Or
dinal) : StrictMono (veblenWith f o)
-/
theorem veblenWith_le_veblenWith_iff_right : veblenWith f o a ≤ veblenWith f o b ↔ a ≤ b :=
  (veblenWith_right_strictMono hf o).le_iff_le
/-
**Ordinal.veblenWith_injective** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：veblenWith_injective (o : Ordinal) : Function.Injective (veblenWith f o)
参数：o : Ordinal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用定理 `Ordinal.veblenWith_right_strictMono`：veblenWith_right_strictMono (o : Or
dinal) : StrictMono (veblenWith f o)
-/
theorem veblenWith_injective (o : Ordinal) : Function.Injective (veblenWith f o) :=
  (veblenWith_right_strictMono hf o).injective

@[simp]
/-
**Ordinal.veblenWith_inj** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：veblenWith_inj : veblenWith f o a = veblenWith f o b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Ordinal.veblenWith_injective`：veblenWith_injective (o : Ordinal) : Funct
ion.Injective (veblenWith f o)
-/
theorem veblenWith_inj : veblenWith f o a = veblenWith f o b ↔ a = b :=
  (veblenWith_injective hf o).eq_iff
/-
**Ordinal.right_le_veblenWith** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：right_le_veblenWith (o a : Ordinal) : a <= veblenWith f o a
参数：o a : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.le_apply`：StrictMono.le_apply [WellFoundedLT β] {f : β -> β} 
(hf : StrictMono f) {x} : x <= f x
· 使用定理 `Ordinal.veblenWith_right_strictMono`：veblenWith_right_strictMono (o : Or
dinal) : StrictMono (veblenWith f o)
-/
theorem right_le_veblenWith (o a : Ordinal) : a ≤ veblenWith f o a :=
  (veblenWith_right_strictMono hf o).le_apply
/-
**Ordinal.veblenWith_left_monotone** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：veblenWith_left_monotone (a : Ordinal) : Monotone (veblenWith f · a)
参数：a : Ordinal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `monotone_iff_forall_lt`：monotone_iff_forall_lt : Monotone f ↔ forall ⦃a 
b⦄, a < b -> f a <= f b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.veblenWith_veblenWith_of_lt`：veblenWith_veblenWith_of_lt (h : o₁
 < o₂) (a : Ordinal) : veblenWith f o₁ (veblenWith f o₂ a) = veblenWith f o₂ a
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `Ordinal.veblenWith_right_strictMono`：veblenWith_right_strictMono (o : Or
dinal) : StrictMono (veblenWith f o)
· 使用定理 `Ordinal.right_le_veblenWith`：right_le_veblenWith (o a : Ordinal) : a <= 
veblenWith f o a
-/
theorem veblenWith_left_monotone (a : Ordinal) : Monotone (veblenWith f · a) := by
  rw [monotone_iff_forall_lt]
  intro o₁ o₂ h
  rw [← veblenWith_veblenWith_of_lt hf h]
  exact (veblenWith_right_strictMono hf o₁).monotone (right_le_veblenWith hf o₂ a)
/-
**Ordinal.veblenWith_pos** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：veblenWith_pos (hp : 0 < f 0) : 0 < veblenWith f o a
参数：hp : 0 < f 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.veblenWith_zero`：veblenWith_zero (f : Ordinal -> Ordinal) : vebl
enWith f 0 = f
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Order.IsNormal.monotone`：∀ {α : Type u_1} {β : Type u_2} [inst : LinearO
rder α] [inst_1 : LinearOrder β] {f : α → β},   Order.IsNormal f → Monotone f
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `eq_zero_or_pos`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero 
α] [IsBotZeroClass α] (a : α), a = 0 ∨ 0 < a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.veblenWith_veblenWith_of_lt`：veblenWith_veblenWith_of_lt (h : o₁
 < o₂) (a : Ordinal) : veblenWith f o₁ (veblenWith f o₂ a) = veblenWith f o₂ a
-/
theorem veblenWith_pos (hp : 0 < f 0) : 0 < veblenWith f o a := by
  have H (b) : 0 < veblenWith f 0 b := by
    rw [veblenWith_zero]
    exact hp.trans_le (hf.monotone zero_le)
  obtain rfl | h := eq_zero_or_pos o
  · exact H a
  · rw [← veblenWith_veblenWith_of_lt hf h]
    exact H _
/-
**Ordinal.veblenWith_zero_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：veblenWith_zero_strictMono (hp : 0 < f 0) : StrictMono (veblenWith f · 0)
参数：hp : 0 < f 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.veblenWith_veblenWith_of_lt`：veblenWith_veblenWith_of_lt (h : o₁
 < o₂) (a : Ordinal) : veblenWith f o₁ (veblenWith f o₂ a) = veblenWith f o₂ a
· 使用定理 `Ordinal.veblenWith_lt_veblenWith_iff_right`：veblenWith_lt_veblenWith_iff
_right : veblenWith f o a < veblenWith f o b ↔ a < b
· 使用定理 `Ordinal.veblenWith_pos`：veblenWith_pos (hp : 0 < f 0) : 0 < veblenWith f
 o a
-/
theorem veblenWith_zero_strictMono (hp : 0 < f 0) : StrictMono (veblenWith f · 0) := by
  intro o₁ o₂ h
  dsimp only
  rw [← veblenWith_veblenWith_of_lt hf h, veblenWith_lt_veblenWith_iff_right hf]
  exact veblenWith_pos hf hp
/-
**Ordinal.veblenWith_zero_lt_veblenWith_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`
。
形式化陈述：veblenWith_zero_lt_veblenWith_zero (hp : 0 < f 0) : veblenWith f o₁ 0 < ve
blenWith f o₂ 0 ↔ o₁ < o₂
参数：hp : 0 < f 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用定理 `Ordinal.veblenWith_zero_strictMono`：veblenWith_zero_strictMono (hp : 0 <
 f 0) : StrictMono (veblenWith f · 0)
-/
theorem veblenWith_zero_lt_veblenWith_zero (hp : 0 < f 0) :
    veblenWith f o₁ 0 < veblenWith f o₂ 0 ↔ o₁ < o₂ :=
  (veblenWith_zero_strictMono hf hp).lt_iff_lt
/-
**Ordinal.veblenWith_zero_le_veblenWith_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`
。
形式化陈述：veblenWith_zero_le_veblenWith_zero (hp : 0 < f 0) : veblenWith f o₁ 0 <= v
eblenWith f o₂ 0 ↔ o₁ <= o₂
参数：hp : 0 < f 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用定理 `Ordinal.veblenWith_zero_strictMono`：veblenWith_zero_strictMono (hp : 0 <
 f 0) : StrictMono (veblenWith f · 0)
-/
theorem veblenWith_zero_le_veblenWith_zero (hp : 0 < f 0) :
    veblenWith f o₁ 0 ≤ veblenWith f o₂ 0 ↔ o₁ ≤ o₂ :=
  (veblenWith_zero_strictMono hf hp).le_iff_le
/-
**Ordinal.veblenWith_zero_inj** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：veblenWith_zero_inj (hp : 0 < f 0) : veblenWith f o₁ 0 = veblenWith f o₂ 0
 ↔ o₁ = o₂
参数：hp : 0 < f 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用定理 `Ordinal.veblenWith_zero_strictMono`：veblenWith_zero_strictMono (hp : 0 <
 f 0) : StrictMono (veblenWith f · 0)
-/
theorem veblenWith_zero_inj (hp : 0 < f 0) : veblenWith f o₁ 0 = veblenWith f o₂ 0 ↔ o₁ = o₂ :=
  (veblenWith_zero_strictMono hf hp).injective.eq_iff
/-
**Ordinal.left_le_veblenWith** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：left_le_veblenWith (hp : 0 < f 0) (o a : Ordinal) : o <= veblenWith f o a
参数：hp : 0 < f 0；o a : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `StrictMono.le_apply`：StrictMono.le_apply [WellFoundedLT β] {f : β -> β} 
(hf : StrictMono f) {x} : x <= f x
· 使用定理 `Ordinal.veblenWith_zero_strictMono`：veblenWith_zero_strictMono (hp : 0 <
 f 0) : StrictMono (veblenWith f · 0)
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `Ordinal.veblenWith_right_strictMono`：veblenWith_right_strictMono (o : Or
dinal) : StrictMono (veblenWith f o)
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
-/
theorem left_le_veblenWith (hp : 0 < f 0) (o a : Ordinal) : o ≤ veblenWith f o a :=
  (veblenWith_zero_strictMono hf hp).le_apply.trans <|
    (veblenWith_right_strictMono hf _).monotone zero_le
/-
**Ordinal.isNormal_veblenWith_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isNormal_veblenWith_zero (hp : 0 < f 0) : IsNormal (veblenWith f · 0)
参数：hp : 0 < f 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.isNormal_iff`：isNormal_iff [LinearOrder α] [LinearOrder β] {f : α 
-> β} : IsNormal f ↔ StrictMono f ∧ forall o, IsSuccLimit o -> forall a, (forall
 b < o, …
· 使用定理 `Ordinal.veblenWith_zero_strictMono`：veblenWith_zero_strictMono (hp : 0 <
 f 0) : StrictMono (veblenWith f · 0)
· 使用定理 `Ordinal.veblenWith_of_ne_zero`：veblenWith_of_ne_zero (f : Ordinal -> Ord
inal) (h : o != 0) : veblenWith f o = derivFamily fun x : Iio o => veblenWith f 
x.1
· 使用定理 `Order.IsSuccLimit.ne_bot`：∀ {α : Type u_1} {a : α} [inst : Preorder α] [
inst_1 : OrderBot α], Order.IsSuccLimit a → a ≠ ⊥
· 使用定理 `Ordinal.derivFamily_zero`：derivFamily_zero (f : ι -> Ordinal -> Ordinal)
 : derivFamily f 0 = nfpFamily f 0
· 使用定理 `Ordinal.nfpFamily_le`：nfpFamily_le {a b} : (forall l, List.foldr f a l <
= b) -> nfpFamily f a <= b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Ordinal.veblenWith_zero`：veblenWith_zero (f : Ordinal -> Ordinal) : vebl
enWith f 0 = f
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `Order.IsSuccLimit.bot_lt`：∀ {α : Type u_1} {a : α} [inst : Preorder α] [
inst_1 : OrderBot α], Order.IsSuccLimit a → ⊥ < a
· 使用定理 `Order.IsSuccLimit.succ_lt`：∀ {α : Type u_1} {a b : α} [inst : PartialOrd
er α] [inst_1 : SuccOrder α],   Order.IsSuccLimit b → a < b → Order.succ a < b
· 使用定理 `max_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, b < a → c <
 a → max b c < a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `Ordinal.veblenWith_right_strictMono`：veblenWith_right_strictMono (o : Or
dinal) : StrictMono (veblenWith f o)
· 使用定理 `Ordinal.veblenWith_left_monotone`：veblenWith_left_monotone (a : Ordinal)
 : Monotone (veblenWith f · a)
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `Order.le_succ`：le_succ : forall a : α, a <= succ a
· 使用定理 `Ordinal.veblenWith_veblenWith_of_lt`：veblenWith_veblenWith_of_lt (h : o₁
 < o₂) (a : Ordinal) : veblenWith f o₁ (veblenWith f o₂ a) = veblenWith f o₂ a
· 使用定理 `Order.lt_succ_iff`：lt_succ_iff : a < succ b ↔ a <= b
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem isNormal_veblenWith_zero (hp : 0 < f 0) : IsNormal (veblenWith f · 0) := by
  rw [isNormal_iff]
  refine ⟨veblenWith_zero_strictMono hf hp, fun o ho a IH ↦ ?_⟩
  rw [veblenWith_of_ne_zero f ho.ne_bot, derivFamily_zero]
  apply nfpFamily_le fun l ↦ ?_
  suffices ∃ b < o, List.foldr _ 0 l ≤ veblenWith f b 0 by
    obtain ⟨b, hb, hb'⟩ := this
    exact hb'.trans (IH b hb)
  induction l with
  | nil => use 0; simpa using ho.bot_lt
  | cons a l IH =>
    obtain ⟨b, hb, hb'⟩ := IH
    refine ⟨_, ho.succ_lt (max_lt a.2 hb), ((veblenWith_right_strictMono hf _).monotone <|
      hb'.trans <| veblenWith_left_monotone hf _ <|
        (le_max_right a.1 b).trans (le_succ _)).trans ?_⟩
    rw [veblenWith_veblenWith_of_lt hf]
    rw [lt_succ_iff]
    exact le_max_left _ b
/-
**Ordinal.veblenWith_veblenWith_eq_veblenWith_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ord
inal`。
形式化陈述：veblenWith_veblenWith_eq_veblenWith_iff (h : o₂ <= o₁) : veblenWith f o₁ (
veblenWith f o₂ a) = veblenWith f o₂ a ↔ veblenWith f o₁ a = a
参数：h : o₂ <= o₁。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem veblenWith_veblenWith_eq_veblenWith_iff (h : o₂ ≤ o₁) :
    veblenWith f o₁ (veblenWith f o₂ a) = veblenWith f o₂ a ↔ veblenWith f o₁ a = a := by
  grind [veblenWith_inj, → veblenWith_eq_self_of_le]
/-
**Ordinal.veblenWith_lt_veblenWith_veblenWith_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ord
inal`。
形式化陈述：veblenWith_lt_veblenWith_veblenWith_iff (h : o₂ <= o₁) : veblenWith f o₂ a
 < veblenWith f o₁ (veblenWith f o₂ a) ↔ a < veblenWith f o₁ a
参数：h : o₂ <= o₁。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LE.le.lt_iff_ne'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b 
≤ a → (b < a ↔ a ≠ b)
· 使用定理 `Ordinal.right_le_veblenWith`：right_le_veblenWith (o a : Ordinal) : a <= 
veblenWith f o a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ordinal.veblenWith_veblenWith_eq_veblenWith_iff`：veblenWith_veblenWith_e
q_veblenWith_iff (h : o₂ <= o₁) : veblenWith f o₁ (veblenWith f o₂ a) = veblenWi
th f o₂ a ↔ veblenWith f o₁ a = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem veblenWith_lt_veblenWith_veblenWith_iff (h : o₂ ≤ o₁) :
    veblenWith f o₂ a < veblenWith f o₁ (veblenWith f o₂ a) ↔ a < veblenWith f o₁ a := by
  simp_rw [(right_le_veblenWith hf ..).lt_iff_ne', ne_eq,
    veblenWith_veblenWith_eq_veblenWith_iff hf h]
/-
**Ordinal.veblenWith_apply_eq_apply_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：veblenWith_apply_eq_apply_iff : veblenWith f o (f a) = f a ↔ veblenWith f 
o a = a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Ordinal.veblenWith_zero`：veblenWith_zero (f : Ordinal -> Ordinal) : vebl
enWith f 0 = f
· 使用定理 `Ordinal.veblenWith_veblenWith_eq_veblenWith_iff`：veblenWith_veblenWith_e
q_veblenWith_iff (h : o₂ <= o₁) : veblenWith f o₁ (veblenWith f o₂ a) = veblenWi
th f o₂ a ↔ veblenWith f o₁ a = a
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
-/
theorem veblenWith_apply_eq_apply_iff : veblenWith f o (f a) = f a ↔ veblenWith f o a = a := by
  simpa using veblenWith_veblenWith_eq_veblenWith_iff hf zero_le
/-
**Ordinal.apply_lt_veblenWith_apply_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：apply_lt_veblenWith_apply_iff : f a < veblenWith f o (f a) ↔ a < veblenWit
h f o a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Ordinal.veblenWith_zero`：veblenWith_zero (f : Ordinal -> Ordinal) : vebl
enWith f 0 = f
· 使用定理 `Ordinal.veblenWith_lt_veblenWith_veblenWith_iff`：veblenWith_lt_veblenWit
h_veblenWith_iff (h : o₂ <= o₁) : veblenWith f o₂ a < veblenWith f o₁ (veblenWit
h f o₂ a) ↔ a < veblenWith f o₁ a
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
-/
theorem apply_lt_veblenWith_apply_iff : f a < veblenWith f o (f a) ↔ a < veblenWith f o a := by
  simpa using veblenWith_lt_veblenWith_veblenWith_iff hf zero_le
/-
**Ordinal.cmp_veblenWith** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：cmp_veblenWith : cmp (veblenWith f o₁ a) (veblenWith f o₂ b) = match cmp o
₁ o₂ with | .eq => cmp a b | .lt => cmp a (veblenWith f o₂ b) | .gt => cmp (vebl
enWith f o₁ a) b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.veblenWith_veblenWith_of_lt`：veblenWith_veblenWith_of_lt (h : o₁
 < o₂) (a : Ordinal) : veblenWith f o₁ (veblenWith f o₂ a) = veblenWith f o₂ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `StrictMono.cmp_map_eq`：StrictMono.cmp_map_eq (hf : StrictMono f) (x y : 
α) : cmp (f x) (f y) = cmp x y
· 使用定理 `Ordinal.veblenWith_right_strictMono`：veblenWith_right_strictMono (o : Or
dinal) : StrictMono (veblenWith f o)
· 使用定理 `LT.lt.cmp_eq_lt`：LT.lt.cmp_eq_lt (h : x < y) : cmp x y = Ordering.lt
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `cmp_self_eq_eq`：cmp_self_eq_eq : cmp x x = Ordering.eq
· 使用定理 `LT.lt.cmp_eq_gt`：LT.lt.cmp_eq_gt (h : x < y) : cmp y x = Ordering.gt
-/
theorem cmp_veblenWith :
    cmp (veblenWith f o₁ a) (veblenWith f o₂ b) =
    match cmp o₁ o₂ with
    | .eq => cmp a b
    | .lt => cmp a (veblenWith f o₂ b)
    | .gt => cmp (veblenWith f o₁ a) b := by
  obtain h | rfl | h := lt_trichotomy o₁ o₂
  on_goal 2 => simp [(veblenWith_right_strictMono hf _).cmp_map_eq]
  all_goals
    conv_lhs => rw [← veblenWith_veblenWith_of_lt hf h]
    simp [h.cmp_eq_lt, h.cmp_eq_gt, (veblenWith_right_strictMono hf _).cmp_map_eq]

/-- `veblenWith f o₁ a < veblenWith f o₂ b` iff one of the following holds:
* `o₁ = o₂` and `a < b`
* `o₁ < o₂` and `a < veblenWith f o₂ b`
* `o₁ > o₂` and `veblenWith f o₁ a < b` -/
/-
**Ordinal.veblenWith_lt_veblenWith_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：veblenWith_lt_veblenWith_iff : veblenWith f o₁ a < veblenWith f o₂ b ↔ o₁ 
= o₂ ∧ a < b ∨ o₁ < o₂ ∧ a < veblenWith f o₂ b ∨ o₂ < o₁ ∧ veblenWith f o₁ a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `cmp_eq_lt_iff`：cmp_eq_lt_iff : cmp x y = Ordering.lt ↔ x < y
· 使用定理 `Ordinal.cmp_veblenWith`：cmp_veblenWith : cmp (veblenWith f o₁ a) (veblen
With f o₂ b) = match cmp o₁ o₂ with | .eq => cmp a b | .lt => cmp a (veblenWith 
f o₂ b) | .g…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `cmp.congr_simp`：∀ {α : Type u} [inst : LT α] {inst_1 : DecidableLT α} [i
nst_2 : DecidableLT α] (a a_1 : α),   a = a_1 → ∀ (b b_1 : α), b = b_1 → cmp a b
 = c…
· 使用定理 `cmp_self_eq_eq`：cmp_self_eq_eq : cmp x x = Ordering.eq

--- 原说明 ---
`veblenWith f o₁ a < veblenWith f o₂ b` iff one of the following holds:
* `o₁ = o₂` and `a < b`
* `o₁ < o₂` and `a < veblenWith f o₂ b`
* `o₁ > o₂` and `veblenWith f o₁ a < b`
-/
theorem veblenWith_lt_veblenWith_iff :
    veblenWith f o₁ a < veblenWith f o₂ b ↔
      o₁ = o₂ ∧ a < b ∨ o₁ < o₂ ∧ a < veblenWith f o₂ b ∨ o₂ < o₁ ∧ veblenWith f o₁ a < b := by
  rw [← cmp_eq_lt_iff, cmp_veblenWith hf]
  aesop (add simp lt_asymm)

/-- `veblenWith f o₁ a ≤ veblenWith f o₂ b` iff one of the following holds:
* `o₁ = o₂` and `a ≤ b`
* `o₁ < o₂` and `a ≤ veblenWith f o₂ b`
* `o₁ > o₂` and `veblenWith f o₁ a ≤ b` -/
/-
**Ordinal.veblenWith_le_veblenWith_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：veblenWith_le_veblenWith_iff : veblenWith f o₁ a <= veblenWith f o₂ b ↔ o₁
 = o₂ ∧ a <= b ∨ o₁ < o₂ ∧ a <= veblenWith f o₂ b ∨ o₂ < o₁ ∧ veblenWith f o₁ a 
<= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `cmp_eq_gt_iff`：cmp_eq_gt_iff : cmp x y = Ordering.gt ↔ y < x
· 使用定理 `Ordinal.cmp_veblenWith`：cmp_veblenWith : cmp (veblenWith f o₁ a) (veblen
With f o₂ b) = match cmp o₁ o₂ with | .eq => cmp a b | .lt => cmp a (veblenWith 
f o₂ b) | .g…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `cmp.congr_simp`：∀ {α : Type u} [inst : LT α] {inst_1 : DecidableLT α} [i
nst_2 : DecidableLT α] (a a_1 : α),   a = a_1 → ∀ (b b_1 : α), b = b_1 → cmp a b
 = c…
· 使用定理 `cmp_self_eq_eq`：cmp_self_eq_eq : cmp x x = Ordering.eq

--- 原说明 ---
`veblenWith f o₁ a ≤ veblenWith f o₂ b` iff one of the following holds:
* `o₁ = o₂` and `a ≤ b`
* `o₁ < o₂` and `a ≤ veblenWith f o₂ b`
* `o₁ > o₂` and `veblenWith f o₁ a ≤ b`
-/
theorem veblenWith_le_veblenWith_iff :
    veblenWith f o₁ a ≤ veblenWith f o₂ b ↔
      o₁ = o₂ ∧ a ≤ b ∨ o₁ < o₂ ∧ a ≤ veblenWith f o₂ b ∨ o₂ < o₁ ∧ veblenWith f o₁ a ≤ b := by
  rw [← not_lt, ← cmp_eq_gt_iff, cmp_veblenWith hf]
  aesop (add simp [not_lt_of_ge, lt_asymm])

/-- `veblenWith f o₁ a = veblenWith f o₂ b` iff one of the following holds:
* `o₁ = o₂` and `a = b`
* `o₁ < o₂` and `a = veblenWith f o₂ b`
* `o₁ > o₂` and `veblenWith f o₁ a = b` -/
/-
**Ordinal.veblenWith_eq_veblenWith_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：veblenWith_eq_veblenWith_iff : veblenWith f o₁ a = veblenWith f o₂ b ↔ o₁ 
= o₂ ∧ a = b ∨ o₁ < o₂ ∧ a = veblenWith f o₂ b ∨ o₂ < o₁ ∧ veblenWith f o₁ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `cmp_eq_eq_iff`：cmp_eq_eq_iff : cmp x y = Ordering.eq ↔ x = y
· 使用定理 `Ordinal.cmp_veblenWith`：cmp_veblenWith : cmp (veblenWith f o₁ a) (veblen
With f o₂ b) = match cmp o₁ o₂ with | .eq => cmp a b | .lt => cmp a (veblenWith 
f o₂ b) | .g…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `cmp.congr_simp`：∀ {α : Type u} [inst : LT α] {inst_1 : DecidableLT α} [i
nst_2 : DecidableLT α] (a a_1 : α),   a = a_1 → ∀ (b b_1 : α), b = b_1 → cmp a b
 = c…
· 使用定理 `cmp_self_eq_eq`：cmp_self_eq_eq : cmp x x = Ordering.eq
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
`veblenWith f o₁ a = veblenWith f o₂ b` iff one of the following holds:
* `o₁ = o₂` and `a = b`
* `o₁ < o₂` and `a = veblenWith f o₂ b`
* `o₁ > o₂` and `veblenWith f o₁ a = b`
-/
theorem veblenWith_eq_veblenWith_iff :
    veblenWith f o₁ a = veblenWith f o₂ b ↔
      o₁ = o₂ ∧ a = b ∨ o₁ < o₂ ∧ a = veblenWith f o₂ b ∨ o₂ < o₁ ∧ veblenWith f o₁ a = b := by
  rw [← cmp_eq_eq_iff, cmp_veblenWith hf]
  aesop (add simp lt_asymm)

end veblenWith

/-! ### Veblen function -/

section veblen

/-- `veblen o` is the `o`-th function in the Veblen hierarchy starting with `ω ^ ·`. That is:

- `veblen 0 a = ω ^ a`.
- `veblen o` for `o ≠ 0` enumerates the fixed points of `veblen o'` for `o' < o`.
-/
@[pp_nodot]
/-
**Ordinal.veblen** 是 Mathlib 中的一个定义，位于命名空间 `Ordinal`。
形式化陈述：veblen : Ordinal.{u} -> Ordinal.{u} -> Ordinal.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`veblen o` is the `o`-th function in the Veblen hierarchy starting with `ω ^ ·`.
 That is:

- `veblen 0 a = ω ^ a`.
- `veblen o` for `o ≠ 0` enumerates the fixed points of `veblen o'` for `o' < o`
.
-/
def veblen : Ordinal.{u} → Ordinal.{u} → Ordinal.{u} :=
  veblenWith (ω ^ ·)

@[simp]
/-
**Ordinal.veblen_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：veblen_zero : veblen 0 = fun a => ω ^ a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.veblen.eq_1`：Ordinal.veblen = Ordinal.veblenWith fun x => Ordina
l.omega0 ^ x
· 使用定理 `Ordinal.veblenWith_zero`：veblenWith_zero (f : Ordinal -> Ordinal) : vebl
enWith f 0 = f
-/
theorem veblen_zero : veblen 0 = fun a ↦ ω ^ a := by
  rw [veblen, veblenWith_zero]
/-
**Ordinal.veblen_zero_apply** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：veblen_zero_apply (a : Ordinal) : veblen 0 a = ω ^ a
参数：a : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.veblen_zero`：veblen_zero : veblen 0 = fun a => ω ^ a
-/
theorem veblen_zero_apply (a : Ordinal) : veblen 0 a = ω ^ a := by
  rw [veblen_zero]
/-
**Ordinal.veblen_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：veblen_of_ne_zero (h : o != 0) : veblen o = derivFamily fun x : Iio o => v
eblen x.1
参数：h : o != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.veblenWith_of_ne_zero`：veblenWith_of_ne_zero (f : Ordinal -> Ord
inal) (h : o != 0) : veblenWith f o = derivFamily fun x : Iio o => veblenWith f 
x.1
-/
theorem veblen_of_ne_zero (h : o ≠ 0) : veblen o = derivFamily fun x : Iio o ↦ veblen x.1 :=
  veblenWith_of_ne_zero _ h
/-
**Ordinal.isNormal_veblen** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isNormal_veblen (o : Ordinal) : IsNormal (veblen o)
参数：o : Ordinal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.isNormal_veblenWith`：isNormal_veblenWith (o : Ordinal) : IsNorma
l (veblenWith f o)
· 使用定理 `Ordinal.isNormal_opow`：isNormal_opow {a : Ordinal} (h : 1 < a) : IsNorma
l (a ^ · : Ordinal -> Ordinal)
· 使用定理 `Ordinal.one_lt_omega0`：one_lt_omega0 : 1 < ω
-/
theorem isNormal_veblen (o : Ordinal) : IsNormal (veblen o) :=
  isNormal_veblenWith (isNormal_opow one_lt_omega0) o
/-
**Ordinal.mem_range_veblen** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：mem_range_veblen (h : o != 0) : a in range (veblen o) ↔ forall b < o, vebl
en b a = a
参数：h : o != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.mem_range_veblenWith`：mem_range_veblenWith (h : o != 0) : a in r
ange (veblenWith f o) ↔ forall b < o, veblenWith f b a = a
· 使用定理 `Ordinal.isNormal_opow`：isNormal_opow {a : Ordinal} (h : 1 < a) : IsNorma
l (a ^ · : Ordinal -> Ordinal)
· 使用定理 `Ordinal.one_lt_omega0`：one_lt_omega0 : 1 < ω
-/
theorem mem_range_veblen (h : o ≠ 0) : a ∈ range (veblen o) ↔ ∀ b < o, veblen b a = a :=
  mem_range_veblenWith (isNormal_opow one_lt_omega0) h
/-
**Ordinal.veblen_veblen_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：veblen_veblen_of_lt (h : o₁ < o₂) (a : Ordinal) : veblen o₁ (veblen o₂ a) 
= veblen o₂ a
参数：h : o₁ < o₂；a : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.veblenWith_veblenWith_of_lt`：veblenWith_veblenWith_of_lt (h : o₁
 < o₂) (a : Ordinal) : veblenWith f o₁ (veblenWith f o₂ a) = veblenWith f o₂ a
· 使用定理 `Ordinal.isNormal_opow`：isNormal_opow {a : Ordinal} (h : 1 < a) : IsNorma
l (a ^ · : Ordinal -> Ordinal)
· 使用定理 `Ordinal.one_lt_omega0`：one_lt_omega0 : 1 < ω
-/
theorem veblen_veblen_of_lt (h : o₁ < o₂) (a : Ordinal) : veblen o₁ (veblen o₂ a) = veblen o₂ a :=
  veblenWith_veblenWith_of_lt (isNormal_opow one_lt_omega0) h a
/-
**Ordinal.veblen_eq_self_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：veblen_eq_self_of_le (h : o₁ <= o₂) (h' : veblen o₂ a = a) : veblen o₁ a =
 a
参数：h : o₁ <= o₂；h' : veblen o₂ a = a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.veblenWith_eq_self_of_le`：veblenWith_eq_self_of_le (h : o₁ <= o₂
) (h' : veblenWith f o₂ a = a) : veblenWith f o₁ a = a
· 使用定理 `Ordinal.isNormal_opow`：isNormal_opow {a : Ordinal} (h : 1 < a) : IsNorma
l (a ^ · : Ordinal -> Ordinal)
· 使用定理 `Ordinal.one_lt_omega0`：one_lt_omega0 : 1 < ω
-/
theorem veblen_eq_self_of_le (h : o₁ ≤ o₂) (h' : veblen o₂ a = a) : veblen o₁ a = a :=
  veblenWith_eq_self_of_le (isNormal_opow one_lt_omega0) h h'
/-
**Ordinal.veblen_mem_range_opow** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：veblen_mem_range_opow (o a : Ordinal) : veblen o a in range (ω ^ · : Ordin
al -> Ordinal)
参数：o a : Ordinal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.veblenWith_mem_range`：veblenWith_mem_range : veblenWith f o a in
 range f
· 使用定理 `Ordinal.isNormal_opow`：isNormal_opow {a : Ordinal} (h : 1 < a) : IsNorma
l (a ^ · : Ordinal -> Ordinal)
· 使用定理 `Ordinal.one_lt_omega0`：one_lt_omega0 : 1 < ω
-/
theorem veblen_mem_range_opow (o a : Ordinal) : veblen o a ∈ range (ω ^ · : Ordinal → Ordinal) :=
  veblenWith_mem_range (isNormal_opow one_lt_omega0)
/-
**Ordinal.veblen_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：veblen_add_one (o : Ordinal) : veblen (o + 1) = deriv (veblen o)
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.veblenWith_add_one`：veblenWith_add_one (o : Ordinal) : veblenWit
h f (o + 1) = deriv (veblenWith f o)
· 使用定理 `Ordinal.isNormal_opow`：isNormal_opow {a : Ordinal} (h : 1 < a) : IsNorma
l (a ^ · : Ordinal -> Ordinal)
· 使用定理 `Ordinal.one_lt_omega0`：one_lt_omega0 : 1 < ω
-/
theorem veblen_add_one (o : Ordinal) : veblen (o + 1) = deriv (veblen o) :=
  veblenWith_add_one (isNormal_opow one_lt_omega0) o

@[deprecated veblen_add_one (since := "2026-02-26")]
/-
**Ordinal.veblen_succ** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：veblen_succ (o : Ordinal) : veblen (succ o) = deriv (veblen o)
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.veblen_add_one`：veblen_add_one (o : Ordinal) : veblen (o + 1) = 
deriv (veblen o)
-/
theorem veblen_succ (o : Ordinal) : veblen (succ o) = deriv (veblen o) :=
  veblen_add_one o
/-
**Ordinal.veblen_right_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：veblen_right_strictMono (o : Ordinal) : StrictMono (veblen o)
参数：o : Ordinal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.veblenWith_right_strictMono`：veblenWith_right_strictMono (o : Or
dinal) : StrictMono (veblenWith f o)
· 使用定理 `Ordinal.isNormal_opow`：isNormal_opow {a : Ordinal} (h : 1 < a) : IsNorma
l (a ^ · : Ordinal -> Ordinal)
· 使用定理 `Ordinal.one_lt_omega0`：one_lt_omega0 : 1 < ω
-/
theorem veblen_right_strictMono (o : Ordinal) : StrictMono (veblen o) :=
  veblenWith_right_strictMono (isNormal_opow one_lt_omega0) o

@[simp]
/-
**Ordinal.veblen_lt_veblen_iff_right** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：veblen_lt_veblen_iff_right : veblen o a < veblen o b ↔ a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.veblenWith_lt_veblenWith_iff_right`：veblenWith_lt_veblenWith_iff
_right : veblenWith f o a < veblenWith f o b ↔ a < b
· 使用定理 `Ordinal.isNormal_opow`：isNormal_opow {a : Ordinal} (h : 1 < a) : IsNorma
l (a ^ · : Ordinal -> Ordinal)
· 使用定理 `Ordinal.one_lt_omega0`：one_lt_omega0 : 1 < ω
-/
theorem veblen_lt_veblen_iff_right : veblen o a < veblen o b ↔ a < b :=
  veblenWith_lt_veblenWith_iff_right (isNormal_opow one_lt_omega0)

@[simp]
/-
**Ordinal.veblen_le_veblen_iff_right** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：veblen_le_veblen_iff_right : veblen o a <= veblen o b ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.veblenWith_le_veblenWith_iff_right`：veblenWith_le_veblenWith_iff
_right : veblenWith f o a <= veblenWith f o b ↔ a <= b
· 使用定理 `Ordinal.isNormal_opow`：isNormal_opow {a : Ordinal} (h : 1 < a) : IsNorma
l (a ^ · : Ordinal -> Ordinal)
· 使用定理 `Ordinal.one_lt_omega0`：one_lt_omega0 : 1 < ω
-/
theorem veblen_le_veblen_iff_right : veblen o a ≤ veblen o b ↔ a ≤ b :=
  veblenWith_le_veblenWith_iff_right (isNormal_opow one_lt_omega0)
/-
**Ordinal.veblen_injective** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：veblen_injective (o : Ordinal) : Function.Injective (veblen o)
参数：o : Ordinal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.veblenWith_injective`：veblenWith_injective (o : Ordinal) : Funct
ion.Injective (veblenWith f o)
· 使用定理 `Ordinal.isNormal_opow`：isNormal_opow {a : Ordinal} (h : 1 < a) : IsNorma
l (a ^ · : Ordinal -> Ordinal)
· 使用定理 `Ordinal.one_lt_omega0`：one_lt_omega0 : 1 < ω
-/
theorem veblen_injective (o : Ordinal) : Function.Injective (veblen o) :=
  veblenWith_injective (isNormal_opow one_lt_omega0) o

@[simp]
/-
**Ordinal.veblen_inj** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：veblen_inj : veblen o a = veblen o b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Ordinal.veblen_injective`：veblen_injective (o : Ordinal) : Function.Inje
ctive (veblen o)
-/
theorem veblen_inj : veblen o a = veblen o b ↔ a = b :=
  (veblen_injective o).eq_iff
/-
**Ordinal.right_le_veblen** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：right_le_veblen (o a : Ordinal) : a <= veblen o a
参数：o a : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.right_le_veblenWith`：right_le_veblenWith (o a : Ordinal) : a <= 
veblenWith f o a
· 使用定理 `Ordinal.isNormal_opow`：isNormal_opow {a : Ordinal} (h : 1 < a) : IsNorma
l (a ^ · : Ordinal -> Ordinal)
· 使用定理 `Ordinal.one_lt_omega0`：one_lt_omega0 : 1 < ω
-/
theorem right_le_veblen (o a : Ordinal) : a ≤ veblen o a :=
  right_le_veblenWith (isNormal_opow one_lt_omega0) o a
/-
**Ordinal.veblen_left_monotone** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：veblen_left_monotone (o : Ordinal) : Monotone (veblen · o)
参数：o : Ordinal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.veblenWith_left_monotone`：veblenWith_left_monotone (a : Ordinal)
 : Monotone (veblenWith f · a)
· 使用定理 `Ordinal.isNormal_opow`：isNormal_opow {a : Ordinal} (h : 1 < a) : IsNorma
l (a ^ · : Ordinal -> Ordinal)
· 使用定理 `Ordinal.one_lt_omega0`：one_lt_omega0 : 1 < ω
-/
theorem veblen_left_monotone (o : Ordinal) : Monotone (veblen · o) :=
  veblenWith_left_monotone (isNormal_opow one_lt_omega0) o

@[simp]
/-
**Ordinal.veblen_pos** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：veblen_pos : 0 < veblen o a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.veblenWith_pos`：veblenWith_pos (hp : 0 < f 0) : 0 < veblenWith f
 o a
· 使用定理 `Ordinal.isNormal_opow`：isNormal_opow {a : Ordinal} (h : 1 < a) : IsNorma
l (a ^ · : Ordinal -> Ordinal)
· 使用定理 `Ordinal.one_lt_omega0`：one_lt_omega0 : 1 < ω
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.opow_zero`：opow_zero (a : Ordinal) : a ^ (0 : Ordinal) = 1
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem veblen_pos : 0 < veblen o a :=
  veblenWith_pos (isNormal_opow one_lt_omega0) (by simp)
/-
**Ordinal.veblen_zero_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：veblen_zero_strictMono : StrictMono (veblen · 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.veblenWith_zero_strictMono`：veblenWith_zero_strictMono (hp : 0 <
 f 0) : StrictMono (veblenWith f · 0)
· 使用定理 `Ordinal.isNormal_opow`：isNormal_opow {a : Ordinal} (h : 1 < a) : IsNorma
l (a ^ · : Ordinal -> Ordinal)
· 使用定理 `Ordinal.one_lt_omega0`：one_lt_omega0 : 1 < ω
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.opow_zero`：opow_zero (a : Ordinal) : a ^ (0 : Ordinal) = 1
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem veblen_zero_strictMono : StrictMono (veblen · 0) :=
  veblenWith_zero_strictMono (isNormal_opow one_lt_omega0) (by simp)

@[simp]
/-
**Ordinal.veblen_zero_lt_veblen_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：veblen_zero_lt_veblen_zero : veblen o₁ 0 < veblen o₂ 0 ↔ o₁ < o₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用定理 `Ordinal.veblen_zero_strictMono`：veblen_zero_strictMono : StrictMono (veb
len · 0)
-/
theorem veblen_zero_lt_veblen_zero : veblen o₁ 0 < veblen o₂ 0 ↔ o₁ < o₂ :=
  veblen_zero_strictMono.lt_iff_lt

@[simp]
/-
**Ordinal.veblen_zero_le_veblen_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：veblen_zero_le_veblen_zero : veblen o₁ 0 <= veblen o₂ 0 ↔ o₁ <= o₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用定理 `Ordinal.veblen_zero_strictMono`：veblen_zero_strictMono : StrictMono (veb
len · 0)
-/
theorem veblen_zero_le_veblen_zero : veblen o₁ 0 ≤ veblen o₂ 0 ↔ o₁ ≤ o₂ :=
  veblen_zero_strictMono.le_iff_le

@[simp]
/-
**Ordinal.veblen_zero_inj** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：veblen_zero_inj : veblen o₁ 0 = veblen o₂ 0 ↔ o₁ = o₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用定理 `Ordinal.veblen_zero_strictMono`：veblen_zero_strictMono : StrictMono (veb
len · 0)
-/
theorem veblen_zero_inj : veblen o₁ 0 = veblen o₂ 0 ↔ o₁ = o₂ :=
  veblen_zero_strictMono.injective.eq_iff
/-
**Ordinal.left_le_veblen** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：left_le_veblen (o a : Ordinal) : o <= veblen o a
参数：o a : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.left_le_veblenWith`：left_le_veblenWith (hp : 0 < f 0) (o a : Ord
inal) : o <= veblenWith f o a
· 使用定理 `Ordinal.isNormal_opow`：isNormal_opow {a : Ordinal} (h : 1 < a) : IsNorma
l (a ^ · : Ordinal -> Ordinal)
· 使用定理 `Ordinal.one_lt_omega0`：one_lt_omega0 : 1 < ω
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.opow_zero`：opow_zero (a : Ordinal) : a ^ (0 : Ordinal) = 1
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem left_le_veblen (o a : Ordinal) : o ≤ veblen o a :=
  left_le_veblenWith (isNormal_opow one_lt_omega0) (by simp) o a
/-
**Ordinal.isNormal_veblen_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isNormal_veblen_zero : IsNormal (veblen · 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.isNormal_veblenWith_zero`：isNormal_veblenWith_zero (hp : 0 < f 0
) : IsNormal (veblenWith f · 0)
· 使用定理 `Ordinal.isNormal_opow`：isNormal_opow {a : Ordinal} (h : 1 < a) : IsNorma
l (a ^ · : Ordinal -> Ordinal)
· 使用定理 `Ordinal.one_lt_omega0`：one_lt_omega0 : 1 < ω
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.opow_zero`：opow_zero (a : Ordinal) : a ^ (0 : Ordinal) = 1
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isNormal_veblen_zero : IsNormal (veblen · 0) :=
  isNormal_veblenWith_zero (isNormal_opow one_lt_omega0) (by simp)
/-
**Ordinal.veblen_veblen_eq_veblen_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：veblen_veblen_eq_veblen_iff (h : o₂ <= o₁) : veblen o₁ (veblen o₂ a) = veb
len o₂ a ↔ veblen o₁ a = a
参数：h : o₂ <= o₁。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.veblenWith_veblenWith_eq_veblenWith_iff`：veblenWith_veblenWith_e
q_veblenWith_iff (h : o₂ <= o₁) : veblenWith f o₁ (veblenWith f o₂ a) = veblenWi
th f o₂ a ↔ veblenWith f o₁ a = a
· 使用定理 `Ordinal.isNormal_opow`：isNormal_opow {a : Ordinal} (h : 1 < a) : IsNorma
l (a ^ · : Ordinal -> Ordinal)
· 使用定理 `Ordinal.one_lt_omega0`：one_lt_omega0 : 1 < ω
-/
theorem veblen_veblen_eq_veblen_iff (h : o₂ ≤ o₁) :
    veblen o₁ (veblen o₂ a) = veblen o₂ a ↔ veblen o₁ a = a :=
  veblenWith_veblenWith_eq_veblenWith_iff (isNormal_opow one_lt_omega0) h
/-
**Ordinal.veblen_lt_veblen_veblen_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：veblen_lt_veblen_veblen_iff (h : o₂ <= o₁) : veblen o₂ a < veblen o₁ (vebl
en o₂ a) ↔ a < veblen o₁ a
参数：h : o₂ <= o₁。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.veblenWith_lt_veblenWith_veblenWith_iff`：veblenWith_lt_veblenWit
h_veblenWith_iff (h : o₂ <= o₁) : veblenWith f o₂ a < veblenWith f o₁ (veblenWit
h f o₂ a) ↔ a < veblenWith f o₁ a
· 使用定理 `Ordinal.isNormal_opow`：isNormal_opow {a : Ordinal} (h : 1 < a) : IsNorma
l (a ^ · : Ordinal -> Ordinal)
· 使用定理 `Ordinal.one_lt_omega0`：one_lt_omega0 : 1 < ω
-/
theorem veblen_lt_veblen_veblen_iff (h : o₂ ≤ o₁) :
    veblen o₂ a < veblen o₁ (veblen o₂ a) ↔ a < veblen o₁ a :=
  veblenWith_lt_veblenWith_veblenWith_iff (isNormal_opow one_lt_omega0) h
/-
**Ordinal.veblen_opow_eq_opow_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：veblen_opow_eq_opow_iff : veblen o (ω ^ a) = ω ^ a ↔ veblen o a = a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.veblenWith_apply_eq_apply_iff`：veblenWith_apply_eq_apply_iff : v
eblenWith f o (f a) = f a ↔ veblenWith f o a = a
· 使用定理 `Ordinal.isNormal_opow`：isNormal_opow {a : Ordinal} (h : 1 < a) : IsNorma
l (a ^ · : Ordinal -> Ordinal)
· 使用定理 `Ordinal.one_lt_omega0`：one_lt_omega0 : 1 < ω
-/
theorem veblen_opow_eq_opow_iff : veblen o (ω ^ a) = ω ^ a ↔ veblen o a = a :=
  veblenWith_apply_eq_apply_iff (isNormal_opow one_lt_omega0)
/-
**Ordinal.opow_lt_veblen_opow_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：opow_lt_veblen_opow_iff : ω ^ a < veblen o (ω ^ a) ↔ a < veblen o a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.apply_lt_veblenWith_apply_iff`：apply_lt_veblenWith_apply_iff : f
 a < veblenWith f o (f a) ↔ a < veblenWith f o a
· 使用定理 `Ordinal.isNormal_opow`：isNormal_opow {a : Ordinal} (h : 1 < a) : IsNorma
l (a ^ · : Ordinal -> Ordinal)
· 使用定理 `Ordinal.one_lt_omega0`：one_lt_omega0 : 1 < ω
-/
theorem opow_lt_veblen_opow_iff : ω ^ a < veblen o (ω ^ a) ↔ a < veblen o a :=
  apply_lt_veblenWith_apply_iff (isNormal_opow one_lt_omega0)
/-
**Ordinal.lt_veblen** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lt_veblen (a : Ordinal) : a < veblen a a
参数：a : Ordinal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_zero_or_pos`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero 
α] [IsBotZeroClass α] (a : α), a = 0 ∨ 0 < a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Ordinal.veblen_zero`：veblen_zero : veblen 0 = fun a => ω ^ a
· 使用定理 `Ordinal.opow_zero`：opow_zero (a : Ordinal) : a ^ (0 : Ordinal) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Ordinal.left_le_veblen`：left_le_veblen (o a : Ordinal) : o <= veblen o a
-/
theorem lt_veblen (a : Ordinal) : a < veblen a a := by
  obtain rfl | h := eq_zero_or_pos a
  · simp
  · apply (left_le_veblen a 0).trans_lt
    simpa
/-
**Ordinal.cmp_veblen** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：cmp_veblen : cmp (veblen o₁ a) (veblen o₂ b) = match cmp o₁ o₂ with | .eq 
=> cmp a b | .lt => cmp a (veblen o₂ b) | .gt => cmp (veblen o₁ a) b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.cmp_veblenWith`：cmp_veblenWith : cmp (veblenWith f o₁ a) (veblen
With f o₂ b) = match cmp o₁ o₂ with | .eq => cmp a b | .lt => cmp a (veblenWith 
f o₂ b) | .g…
· 使用定理 `Ordinal.isNormal_opow`：isNormal_opow {a : Ordinal} (h : 1 < a) : IsNorma
l (a ^ · : Ordinal -> Ordinal)
· 使用定理 `Ordinal.one_lt_omega0`：one_lt_omega0 : 1 < ω
-/
theorem cmp_veblen : cmp (veblen o₁ a) (veblen o₂ b) =
    match cmp o₁ o₂ with
    | .eq => cmp a b
    | .lt => cmp a (veblen o₂ b)
    | .gt => cmp (veblen o₁ a) b :=
  cmp_veblenWith (isNormal_opow one_lt_omega0)

/-- `veblen o₁ a < veblen o₂ b` iff one of the following holds:
* `o₁ = o₂` and `a < b`
* `o₁ < o₂` and `a < veblen o₂ b`
* `o₁ > o₂` and `veblen o₁ a < b` -/
/-
**Ordinal.veblen_lt_veblen_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：veblen_lt_veblen_iff : veblen o₁ a < veblen o₂ b ↔ o₁ = o₂ ∧ a < b ∨ o₁ < 
o₂ ∧ a < veblen o₂ b ∨ o₂ < o₁ ∧ veblen o₁ a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.veblenWith_lt_veblenWith_iff`：veblenWith_lt_veblenWith_iff : veb
lenWith f o₁ a < veblenWith f o₂ b ↔ o₁ = o₂ ∧ a < b ∨ o₁ < o₂ ∧ a < veblenWith 
f o₂ b ∨ o₂ < o₁ ∧ veblenW…
· 使用定理 `Ordinal.isNormal_opow`：isNormal_opow {a : Ordinal} (h : 1 < a) : IsNorma
l (a ^ · : Ordinal -> Ordinal)
· 使用定理 `Ordinal.one_lt_omega0`：one_lt_omega0 : 1 < ω

--- 原说明 ---
`veblen o₁ a < veblen o₂ b` iff one of the following holds:
* `o₁ = o₂` and `a < b`
* `o₁ < o₂` and `a < veblen o₂ b`
* `o₁ > o₂` and `veblen o₁ a < b`
-/
theorem veblen_lt_veblen_iff :
    veblen o₁ a < veblen o₂ b ↔
      o₁ = o₂ ∧ a < b ∨ o₁ < o₂ ∧ a < veblen o₂ b ∨ o₂ < o₁ ∧ veblen o₁ a < b :=
  veblenWith_lt_veblenWith_iff (isNormal_opow one_lt_omega0)

/-- `veblen o₁ a ≤ veblen o₂ b` iff one of the following holds:
* `o₁ = o₂` and `a ≤ b`
* `o₁ < o₂` and `a ≤ veblen o₂ b`
* `o₁ > o₂` and `veblen o₁ a ≤ b` -/
/-
**Ordinal.veblen_le_veblen_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：veblen_le_veblen_iff : veblen o₁ a <= veblen o₂ b ↔ o₁ = o₂ ∧ a <= b ∨ o₁ 
< o₂ ∧ a <= veblen o₂ b ∨ o₂ < o₁ ∧ veblen o₁ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.veblenWith_le_veblenWith_iff`：veblenWith_le_veblenWith_iff : veb
lenWith f o₁ a <= veblenWith f o₂ b ↔ o₁ = o₂ ∧ a <= b ∨ o₁ < o₂ ∧ a <= veblenWi
th f o₂ b ∨ o₂ < o₁ ∧ vebl…
· 使用定理 `Ordinal.isNormal_opow`：isNormal_opow {a : Ordinal} (h : 1 < a) : IsNorma
l (a ^ · : Ordinal -> Ordinal)
· 使用定理 `Ordinal.one_lt_omega0`：one_lt_omega0 : 1 < ω

--- 原说明 ---
`veblen o₁ a ≤ veblen o₂ b` iff one of the following holds:
* `o₁ = o₂` and `a ≤ b`
* `o₁ < o₂` and `a ≤ veblen o₂ b`
* `o₁ > o₂` and `veblen o₁ a ≤ b`
-/
theorem veblen_le_veblen_iff :
    veblen o₁ a ≤ veblen o₂ b ↔
      o₁ = o₂ ∧ a ≤ b ∨ o₁ < o₂ ∧ a ≤ veblen o₂ b ∨ o₂ < o₁ ∧ veblen o₁ a ≤ b :=
  veblenWith_le_veblenWith_iff (isNormal_opow one_lt_omega0)

/-- `veblen o₁ a ≤ veblen o₂ b` iff one of the following holds:
* `o₁ = o₂` and `a = b`
* `o₁ < o₂` and `a = veblen o₂ b`
* `o₁ > o₂` and `veblen o₁ a = b` -/
/-
**Ordinal.veblen_eq_veblen_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：veblen_eq_veblen_iff : veblen o₁ a = veblen o₂ b ↔ o₁ = o₂ ∧ a = b ∨ o₁ < 
o₂ ∧ a = veblen o₂ b ∨ o₂ < o₁ ∧ veblen o₁ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.veblenWith_eq_veblenWith_iff`：veblenWith_eq_veblenWith_iff : veb
lenWith f o₁ a = veblenWith f o₂ b ↔ o₁ = o₂ ∧ a = b ∨ o₁ < o₂ ∧ a = veblenWith 
f o₂ b ∨ o₂ < o₁ ∧ veblenW…
· 使用定理 `Ordinal.isNormal_opow`：isNormal_opow {a : Ordinal} (h : 1 < a) : IsNorma
l (a ^ · : Ordinal -> Ordinal)
· 使用定理 `Ordinal.one_lt_omega0`：one_lt_omega0 : 1 < ω

--- 原说明 ---
`veblen o₁ a ≤ veblen o₂ b` iff one of the following holds:
* `o₁ = o₂` and `a = b`
* `o₁ < o₂` and `a = veblen o₂ b`
* `o₁ > o₂` and `veblen o₁ a = b`
-/
theorem veblen_eq_veblen_iff :
    veblen o₁ a = veblen o₂ b ↔
      o₁ = o₂ ∧ a = b ∨ o₁ < o₂ ∧ a = veblen o₂ b ∨ o₂ < o₁ ∧ veblen o₁ a = b :=
  veblenWith_eq_veblenWith_iff (isNormal_opow one_lt_omega0)

end veblen

/-! ### Inverse Veblen function -/

/-- For any given `x`, there exists a unique pair `(o, a)` such that `ω ^ x = veblen o a` and
`a < ω ^ x`. `invVeblen₁ x` and `invVeblen₂ x` return the first and second entries of this pair,
respectively. See `veblen_eq_opow_iff` for a proof.

Composing this function with `Ordinal.CNF` yields a predicative ordinal notation up to `Γ₀`. -/
/-
**Ordinal.invVeblen** 是 Mathlib 中的一个定义，位于命名空间 `Ordinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For any given `x`, there exists a unique pair `(o, a)` such that `ω ^ x = veblen
 o a` and
`a < ω ^ x`. `invVeblen₁ x` and `invVeblen₂ x` return the first and second entri
es of this pair,
respectively. See `veblen_eq_opow_iff` for a proof.

Composing this function with `Ordinal.CNF` yields a predicative ordinal notation
 up to `Γ₀`.
-/
def invVeblen₁ (x : Ordinal) : Ordinal :=
  sInf {y | veblen y x ≠ x}
/-
**Ordinal.veblen_eq_of_lt_invVeblen** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem veblen_eq_of_lt_invVeblen₁ (h : o < invVeblen₁ x) : veblen o x = x := by
  simpa using notMem_of_lt_csInf' h
/-
**Ordinal.invVeblen** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem invVeblen₁_le (x : Ordinal) : invVeblen₁ x ≤ x :=
  csInf_le' (lt_veblen x).ne'
/-
**Ordinal.lt_veblen_invVeblen** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lt_veblen_invVeblen₁ (x : Ordinal) : x < veblen (invVeblen₁ x) x :=
  (right_le_veblen ..).lt_of_ne' (csInf_mem (s := {y | veblen y x ≠ x}) ⟨x, (lt_veblen x).ne'⟩)
/-
**Ordinal.lt_veblen_iff_invVeblen** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lt_veblen_iff_invVeblen₁_le : a < veblen o a ↔ invVeblen₁ a ≤ o := by
  obtain h | h := lt_or_ge o (invVeblen₁ a)
  · rw [veblen_eq_of_lt_invVeblen₁ h]
    simpa
  · simpa [(lt_veblen_invVeblen₁ a).trans_le (veblen_left_monotone _ h)]
/-
**Ordinal.mem_range_veblen_iff_le_invVeblen** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_range_veblen_iff_le_invVeblen₁ : ω ^ x ∈ range (veblen o) ↔ o ≤ invVeblen₁ x := by
  obtain h | rfl | h := lt_trichotomy o (invVeblen₁ x)
  · exact iff_of_true ⟨_, veblen_opow_eq_opow_iff.2 <| veblen_eq_of_lt_invVeblen₁ h⟩ h.le
  · apply iff_of_true _ le_rfl
    by_cases h : invVeblen₁ x = 0
    · simp [h]
    · simp_rw [mem_range_veblen h, veblen_opow_eq_opow_iff]
      exact fun o ↦ veblen_eq_of_lt_invVeblen₁
  · apply iff_of_false _ h.not_ge
    rintro ⟨z, hz⟩
    have hz' := hz
    rw [← veblen_veblen_of_lt h, hz', veblen_opow_eq_opow_iff] at hz
    exact (lt_veblen_invVeblen₁ x).ne' hz
/-
**Ordinal.invVeblen** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem invVeblen₁_veblen (h : a < veblen o a) : invVeblen₁ (veblen o a) = o := by
  apply le_antisymm
  · rwa [← lt_veblen_iff_invVeblen₁_le, veblen_lt_veblen_iff_right]
  · rw [← mem_range_veblen_iff_le_invVeblen₁]
    obtain rfl | ho := eq_zero_or_pos o
    · simp
    · rw [← veblen_zero_apply, veblen_veblen_of_lt ho]
      simp
/-
**Ordinal.invVeblen** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem invVeblen₁_of_lt_opow (h : a < ω ^ a) : invVeblen₁ a = 0 := by
  rwa [← nonpos_iff_eq_zero, ← lt_veblen_iff_invVeblen₁_le, veblen_zero]

@[simp]
/-
**Ordinal.invVeblen** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem invVeblen₁_zero : invVeblen₁ 0 = 0 :=
  invVeblen₁_of_lt_opow <| by simp

@[inherit_doc invVeblen₁]
/-
**Ordinal.invVeblen** 是 Mathlib 中的一个定义，位于命名空间 `Ordinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def invVeblen₂ (x : Ordinal) : Ordinal :=
  Classical.choose ((mem_range_veblen_iff_le_invVeblen₁ (x := x)).2 le_rfl)

@[simp]
/-
**Ordinal.veblen_invVeblen** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem veblen_invVeblen₁_invVeblen₂ (x : Ordinal) : veblen (invVeblen₁ x) (invVeblen₂ x) = ω ^ x :=
  Classical.choose_spec (mem_range_veblen_iff_le_invVeblen₁.2 le_rfl)
/-
**Ordinal.invVeblen** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem invVeblen₂_eq_iff : invVeblen₂ x = a ↔ ω ^ x = veblen (invVeblen₁ x) a := by
  rw [← veblen_inj (o := x.invVeblen₁), veblen_invVeblen₁_invVeblen₂]
/-
**Ordinal.invVeblen** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem invVeblen₂_lt_iff : invVeblen₂ x < a ↔ ω ^ x < veblen (invVeblen₁ x) a := by
  rw [← veblen_lt_veblen_iff_right (o := x.invVeblen₁), veblen_invVeblen₁_invVeblen₂]
/-
**Ordinal.invVeblen** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem invVeblen₂_le_iff : invVeblen₂ x ≤ a ↔ ω ^ x ≤ veblen (invVeblen₁ x) a := by
  rw [← veblen_le_veblen_iff_right (o := x.invVeblen₁), veblen_invVeblen₁_invVeblen₂]
/-
**Ordinal.lt_invVeblen** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lt_invVeblen₂_iff : a < invVeblen₂ x ↔ veblen (invVeblen₁ x) a < ω ^ x := by
  rw [← veblen_lt_veblen_iff_right (o := x.invVeblen₁), veblen_invVeblen₁_invVeblen₂]
/-
**Ordinal.le_invVeblen** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem le_invVeblen₂_iff : a ≤ invVeblen₂ x ↔ veblen (invVeblen₁ x) a ≤ ω ^ x := by
  rw [← veblen_le_veblen_iff_right (o := x.invVeblen₁), veblen_invVeblen₁_invVeblen₂]
/-
**Ordinal.invVeblen** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem invVeblen₂_lt (x : Ordinal) : invVeblen₂ x < ω ^ x := by
  rw [invVeblen₂_lt_iff, opow_lt_veblen_opow_iff]
  exact lt_veblen_invVeblen₁ x
/-
**Ordinal.invVeblen** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem invVeblen₂_le (x : Ordinal) : invVeblen₂ x ≤ x := by
  obtain h | h := eq_zero_or_pos (invVeblen₁ x)
  · rw [invVeblen₂_le_iff, h, veblen_zero]
  · convert! (invVeblen₂_lt x).le
    rw [← veblen_zero_apply, veblen_eq_of_lt_invVeblen₁ h]
/-
**Ordinal.invVeblen** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem invVeblen₂_of_lt_opow (h : a < ω ^ a) : invVeblen₂ a = a := by
  rw [invVeblen₂_eq_iff, invVeblen₁_of_lt_opow h, veblen_zero_apply]

@[simp]
/-
**Ordinal.invVeblen** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem invVeblen₂_zero : invVeblen₂ 0 = 0 := by
  apply invVeblen₂_of_lt_opow
  simp
/-
**Ordinal.invVeblen** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem invVeblen₂_veblen (ho : o ≠ 0) (h : a < veblen o a) : invVeblen₂ (veblen o a) = a := by
  rw [invVeblen₂_eq_iff, invVeblen₁_veblen h, ← veblen_zero_apply, veblen_veblen_of_lt]
  exact ho.bot_lt
/-
**Ordinal.veblen_eq_opow_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：veblen_eq_opow_iff (h : a < veblen o a) : veblen o a = ω ^ x ↔ invVeblen₁ 
x = o ∧ invVeblen₂ x = a
参数：h : a < veblen o a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_zero_or_pos`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero 
α] [IsBotZeroClass α] (a : α), a = 0 ∨ 0 < a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Ordinal.invVeblen₁_of_lt_opow`：invVeblen₁_of_lt_opow (h : a < ω ^ a) : i
nvVeblen₁ a = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.veblen_zero`：veblen_zero : veblen 0 = fun a => ω ^ a
· 使用定理 `Ordinal.invVeblen₂_of_lt_opow`：invVeblen₂_of_lt_opow (h : a < ω ^ a) : i
nvVeblen₂ a = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.veblen_veblen_of_lt`：veblen_veblen_of_lt (h : o₁ < o₂) (a : Ordi
nal) : veblen o₁ (veblen o₂ a) = veblen o₂ a
· 使用定理 `Ordinal.veblen_zero_apply`：veblen_zero_apply (a : Ordinal) : veblen 0 a 
= ω ^ a
· 使用定理 `Ordinal.opow_right_inj`：opow_right_inj {a b c : Ordinal} (a1 : 1 < a) : 
a ^ b = a ^ c ↔ b = c
· 使用定理 `Ordinal.one_lt_omega0`：one_lt_omega0 : 1 < ω
· 使用定理 `Ordinal.invVeblen₁_veblen`：invVeblen₁_veblen (h : a < veblen o a) : invV
eblen₁ (veblen o a) = o
· 使用定理 `Ordinal.invVeblen₂_veblen`：invVeblen₂_veblen (ho : o != 0) (h : a < vebl
en o a) : invVeblen₂ (veblen o a) = a
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Ordinal.veblen_invVeblen₁_invVeblen₂`：veblen_invVeblen₁_invVeblen₂ (x : 
Ordinal) : veblen (invVeblen₁ x) (invVeblen₂ x) = ω ^ x
-/
theorem veblen_eq_opow_iff (h : a < veblen o a) :
    veblen o a = ω ^ x ↔ invVeblen₁ x = o ∧ invVeblen₂ x = a := by
  refine ⟨?_, fun ⟨hx, ha⟩ ↦ ?_⟩
  · obtain rfl | ho := eq_zero_or_pos o
    · rw [veblen_zero] at h
      have := invVeblen₁_of_lt_opow h
      have := invVeblen₂_of_lt_opow h
      aesop
    · rw [← veblen_veblen_of_lt ho, veblen_zero_apply, opow_right_inj one_lt_omega0]
      rintro rfl
      simp [invVeblen₁_veblen h, invVeblen₂_veblen ho.ne' h]
  · convert! ← veblen_invVeblen₁_invVeblen₂ x

/-! ### Epsilon function -/

/-- The epsilon function enumerates the fixed points of `ω ^ ⬝`.
This is an abbreviation for `veblen 1`. -/
/-
**Ordinal.epsilon** 是 Mathlib 中的一个缩写定义，位于命名空间 `Ordinal`。
形式化陈述：epsilon
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The epsilon function enumerates the fixed points of `ω ^ ⬝`.
This is an abbreviation for `veblen 1`.
-/
abbrev epsilon := veblen 1

@[inherit_doc] scoped notation "ε_ " => epsilon
recommended_spelling "epsilon" for "ε_ " in [epsilon, «termε_»]

/-- `ε₀` is the first fixed point of `ω ^ ⬝`, i.e. the supremum of `ω`, `ω ^ ω`, `ω ^ ω ^ ω`, … -/
scoped notation "ε₀" => ε_ 0
recommended_spelling "epsilon_zero" for "ε₀" in [«termε₀»]

/-
**Ordinal.epsilon_eq_deriv** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：epsilon_eq_deriv (o : Ordinal) : ε_ o = deriv (fun a => ω ^ a) o
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Ordinal.veblen_zero`：veblen_zero : veblen 0 = fun a => ω ^ a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Ordinal.veblen_add_one`：veblen_add_one (o : Ordinal) : veblen (o + 1) = 
deriv (veblen o)
-/
theorem epsilon_eq_deriv (o : Ordinal) : ε_ o = deriv (fun a ↦ ω ^ a) o := by
  simpa [epsilon] using congrFun (veblen_add_one 0) o
/-
**Ordinal.epsilon_zero_eq_nfp** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：epsilon_zero_eq_nfp : ε₀ = nfp (fun a => ω ^ a) 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.epsilon_eq_deriv`：epsilon_eq_deriv (o : Ordinal) : ε_ o = deriv 
(fun a => ω ^ a) o
· 使用定理 `Ordinal.deriv_zero_right`：deriv_zero_right (f) : deriv f 0 = nfp f 0
-/
theorem epsilon_zero_eq_nfp : ε₀ = nfp (fun a ↦ ω ^ a) 0 := by
  rw [epsilon_eq_deriv, deriv_zero_right]

@[deprecated (since := "2026-02-02")]
alias epsilon0_eq_nfp := epsilon_zero_eq_nfp
/-
**Ordinal.epsilon_succ_eq_nfp** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：epsilon_succ_eq_nfp (o : Ordinal) : ε_ (succ o) = nfp (fun a => ω ^ a) (su
cc (ε_ o))
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.epsilon_eq_deriv`：epsilon_eq_deriv (o : Ordinal) : ε_ o = deriv 
(fun a => ω ^ a) o
· 使用定理 `Ordinal.deriv_succ`：deriv_succ (f o) : deriv f (succ o) = nfp f (succ (d
eriv f o))
-/
theorem epsilon_succ_eq_nfp (o : Ordinal) : ε_ (succ o) = nfp (fun a ↦ ω ^ a) (succ (ε_ o)) := by
  rw [epsilon_eq_deriv, epsilon_eq_deriv, deriv_succ]
/-
**Ordinal.epsilon_zero_le_of_omega0_opow_le** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：epsilon_zero_le_of_omega0_opow_le (h : ω ^ o <= o) : ε₀ <= o
参数：h : ω ^ o <= o。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.epsilon_zero_eq_nfp`：epsilon_zero_eq_nfp : ε₀ = nfp (fun a => ω 
^ a) 0
· 使用定理 `Ordinal.nfp_le_fp`：nfp_le_fp (H : Monotone f) {a b} (ab : a <= b) (h : f
 b <= b) : nfp f a <= b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ordinal.opow_le_opow_iff_right`：opow_le_opow_iff_right {a b c : Ordinal}
 (a1 : 1 < a) : a ^ b <= a ^ c ↔ b <= c
· 使用定理 `Ordinal.one_lt_omega0`：one_lt_omega0 : 1 < ω
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
-/
theorem epsilon_zero_le_of_omega0_opow_le (h : ω ^ o ≤ o) : ε₀ ≤ o := by
  rw [epsilon_zero_eq_nfp]
  exact nfp_le_fp (fun _ _ ↦ (opow_le_opow_iff_right one_lt_omega0).2) zero_le h

@[deprecated (since := "2026-02-02")]
alias epsilon0_le_of_omega0_opow_le := epsilon_zero_le_of_omega0_opow_le

@[simp]
/-
**Ordinal.omega0_opow_epsilon** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：omega0_opow_epsilon (o : Ordinal) : ω ^ ε_ o = ε_ o
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.epsilon_eq_deriv`：epsilon_eq_deriv (o : Ordinal) : ε_ o = deriv 
(fun a => ω ^ a) o
· 使用定理 `Ordinal.deriv_fp`：deriv_fp (H : IsNormal f) : forall o, f (deriv f o) = 
deriv f o
· 使用定理 `Ordinal.isNormal_opow`：isNormal_opow {a : Ordinal} (h : 1 < a) : IsNorma
l (a ^ · : Ordinal -> Ordinal)
· 使用定理 `Ordinal.one_lt_omega0`：one_lt_omega0 : 1 < ω
-/
theorem omega0_opow_epsilon (o : Ordinal) : ω ^ ε_ o = ε_ o := by
  rw [epsilon_eq_deriv, deriv_fp (isNormal_opow one_lt_omega0)]

/-- `ε₀` is the limit of `0`, `ω ^ 0`, `ω ^ ω ^ 0`, … -/
/-
**Ordinal.lt_epsilon_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lt_epsilon_zero : o < ε₀ ↔ exists n : Nat, o < (fun a => ω ^ a)^[n] 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.epsilon_zero_eq_nfp`：epsilon_zero_eq_nfp : ε₀ = nfp (fun a => ω 
^ a) 0
· 使用定理 `Ordinal.lt_nfp_iff`：lt_nfp_iff {a b} : a < nfp f b ↔ exists n, a < f^[n]
 b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
`ε₀` is the limit of `0`, `ω ^ 0`, `ω ^ ω ^ 0`, …
-/
theorem lt_epsilon_zero : o < ε₀ ↔ ∃ n : ℕ, o < (fun a ↦ ω ^ a)^[n] 0 := by
  rw [epsilon_zero_eq_nfp, lt_nfp_iff]

@[deprecated (since := "2026-02-02")]
alias lt_epsilon0 := lt_epsilon_zero

/-- `ω ^ ω ^ … ^ 0 < ε₀` -/
/-
**Ordinal.iterate_omega0_opow_lt_epsilon_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal
`。
形式化陈述：iterate_omega0_opow_lt_epsilon_zero (n : Nat) : (fun a => ω ^ a)^[n] 0 < ε
₀
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.epsilon_zero_eq_nfp`：epsilon_zero_eq_nfp : ε₀ = nfp (fun a => ω 
^ a) 0
· 使用定理 `Ordinal.iterate_lt_nfp`：iterate_lt_nfp (hf : StrictMono f) {a} (h : a < 
f a) (n : Nat) : f^[n] a < nfp f a
· 使用定理 `Order.IsNormal.strictMono`：∀ {α : Type u_1} {β : Type u_2} [inst : Linea
rOrder α] [inst_1 : LinearOrder β] {f : α → β},   Order.IsNormal f → StrictMono 
f
· 使用定理 `Ordinal.isNormal_opow`：isNormal_opow {a : Ordinal} (h : 1 < a) : IsNorma
l (a ^ · : Ordinal -> Ordinal)
· 使用定理 `Ordinal.one_lt_omega0`：one_lt_omega0 : 1 < ω
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ordinal.opow_zero`：opow_zero (a : Ordinal) : a ^ (0 : Ordinal) = 1
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`ω ^ ω ^ … ^ 0 < ε₀`
-/
theorem iterate_omega0_opow_lt_epsilon_zero (n : ℕ) : (fun a ↦ ω ^ a)^[n] 0 < ε₀ := by
  rw [epsilon_zero_eq_nfp]
  apply iterate_lt_nfp (isNormal_opow one_lt_omega0).strictMono
  simp

@[deprecated (since := "2026-02-02")]
alias iterate_omega0_opow_lt_epsilon0 := iterate_omega0_opow_lt_epsilon_zero
/-
**Ordinal.omega0_lt_epsilon** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：omega0_lt_epsilon (o : Ordinal) : ω < ε_ o
参数：o : Ordinal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Function.iterate_one`：iterate_one : f^[1] = f
· 使用定理 `Ordinal.opow_zero`：opow_zero (a : Ordinal) : a ^ (0 : Ordinal) = 1
· 使用定理 `Ordinal.opow_one`：opow_one (a : Ordinal) : a ^ (1 : Ordinal) = a
· 使用定理 `Ordinal.iterate_omega0_opow_lt_epsilon_zero`：iterate_omega0_opow_lt_epsi
lon_zero (n : Nat) : (fun a => ω ^ a)^[n] 0 < ε₀
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `Ordinal.veblen_right_strictMono`：veblen_right_strictMono (o : Ordinal) :
 StrictMono (veblen o)
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
-/
theorem omega0_lt_epsilon (o : Ordinal) : ω < ε_ o := by
  apply lt_of_lt_of_le _ <| (veblen_right_strictMono _).monotone zero_le
  simpa using iterate_omega0_opow_lt_epsilon_zero 2
/-
**Ordinal.natCast_lt_epsilon** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：natCast_lt_epsilon (n : Nat) (o : Ordinal) : n < ε_ o
参数：n : Nat；o : Ordinal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Ordinal.natCast_lt_omega0`：natCast_lt_omega0 (n : Nat) : ↑n < ω
· 使用定理 `Ordinal.omega0_lt_epsilon`：omega0_lt_epsilon (o : Ordinal) : ω < ε_ o
-/
theorem natCast_lt_epsilon (n : ℕ) (o : Ordinal) : n < ε_ o :=
  (natCast_lt_omega0 n).trans <| omega0_lt_epsilon o
/-
**Ordinal.epsilon_pos** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：epsilon_pos (o : Ordinal) : 0 < ε_ o
参数：o : Ordinal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.veblen_pos`：veblen_pos : 0 < veblen o a
-/
theorem epsilon_pos (o : Ordinal) : 0 < ε_ o :=
  veblen_pos
/-
**Ordinal.invVeblen** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem invVeblen₁_epsilon (h : o < ε_ o) : invVeblen₁ (ε_ o) = 1 :=
  invVeblen₁_veblen h
/-
**Ordinal.invVeblen** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem invVeblen₂_epsilon (h : o < ε_ o) : invVeblen₂ (ε_ o) = o :=
  invVeblen₂_veblen one_ne_zero h

/-! ### Gamma function -/

/-- The gamma function enumerates the fixed points of `veblen · 0`.

Of particular importance is `Γ₀ = gamma 0`, the Feferman-Schütte ordinal. -/
/-
**Ordinal.gamma** 是 Mathlib 中的一个定义，位于命名空间 `Ordinal`。
形式化陈述：gamma : Ordinal -> Ordinal
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The gamma function enumerates the fixed points of `veblen · 0`.

Of particular importance is `Γ₀ = gamma 0`, the Feferman-Schütte ordinal.
-/
def gamma : Ordinal → Ordinal :=
  deriv (veblen · 0)

@[inherit_doc] scoped notation "Γ_ " => gamma
recommended_spelling "gamma" for "Γ_ " in [gamma, «termΓ_»]

/-- The Feferman-Schütte ordinal `Γ₀` is the smallest fixed point of `veblen · 0`, i.e. the supremum
of `veblen ε₀ 0`, `veblen (veblen ε₀ 0) 0`, etc. -/
scoped notation "Γ₀" => Γ_ 0
recommended_spelling "gamma_zero" for "Γ₀" in [«termΓ₀»]

/-
**Ordinal.isNormal_gamma** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isNormal_gamma : IsNormal gamma
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.isNormal_deriv`：isNormal_deriv (f) : IsNormal (deriv f)
-/
theorem isNormal_gamma : IsNormal gamma :=
  isNormal_deriv _
/-
**Ordinal.mem_range_gamma** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：mem_range_gamma : o in range Γ_ ↔ veblen o 0 = o
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.mem_range_deriv`：mem_range_deriv (H : IsNormal f) {a} : a in Set
.range (deriv f) ↔ f a = a
· 使用定理 `Ordinal.isNormal_veblen_zero`：isNormal_veblen_zero : IsNormal (veblen · 
0)
-/
theorem mem_range_gamma : o ∈ range Γ_ ↔ veblen o 0 = o :=
  mem_range_deriv isNormal_veblen_zero
/-
**Ordinal.strictMono_gamma** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：strictMono_gamma : StrictMono gamma
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsNormal.strictMono`：∀ {α : Type u_1} {β : Type u_2} [inst : Linea
rOrder α] [inst_1 : LinearOrder β] {f : α → β},   Order.IsNormal f → StrictMono 
f
· 使用定理 `Ordinal.isNormal_gamma`：isNormal_gamma : IsNormal gamma
-/
theorem strictMono_gamma : StrictMono gamma :=
  isNormal_gamma.strictMono
/-
**Ordinal.monotone_gamma** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：monotone_gamma : Monotone gamma
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsNormal.monotone`：∀ {α : Type u_1} {β : Type u_2} [inst : LinearO
rder α] [inst_1 : LinearOrder β] {f : α → β},   Order.IsNormal f → Monotone f
· 使用定理 `Ordinal.isNormal_gamma`：isNormal_gamma : IsNormal gamma
-/
theorem monotone_gamma : Monotone gamma :=
  isNormal_gamma.monotone

@[simp]
/-
**Ordinal.gamma_lt_gamma** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：gamma_lt_gamma : Γ_ a < Γ_ b ↔ a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用定理 `Ordinal.strictMono_gamma`：strictMono_gamma : StrictMono gamma
-/
theorem gamma_lt_gamma : Γ_ a < Γ_ b ↔ a < b :=
  strictMono_gamma.lt_iff_lt

@[simp]
/-
**Ordinal.gamma_le_gamma** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：gamma_le_gamma : Γ_ a <= Γ_ b ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用定理 `Ordinal.strictMono_gamma`：strictMono_gamma : StrictMono gamma
-/
theorem gamma_le_gamma : Γ_ a ≤ Γ_ b ↔ a ≤ b :=
  strictMono_gamma.le_iff_le

@[simp]
/-
**Ordinal.gamma_inj** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：gamma_inj : Γ_ a = Γ_ b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用定理 `Ordinal.strictMono_gamma`：strictMono_gamma : StrictMono gamma
-/
theorem gamma_inj : Γ_ a = Γ_ b ↔ a = b :=
  strictMono_gamma.injective.eq_iff

@[simp]
/-
**Ordinal.veblen_gamma_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：veblen_gamma_zero (o : Ordinal) : veblen (Γ_ o) 0 = Γ_ o
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.deriv_fp`：deriv_fp (H : IsNormal f) : forall o, f (deriv f o) = 
deriv f o
· 使用定理 `Ordinal.isNormal_veblen_zero`：isNormal_veblen_zero : IsNormal (veblen · 
0)
-/
theorem veblen_gamma_zero (o : Ordinal) : veblen (Γ_ o) 0 = Γ_ o :=
  deriv_fp isNormal_veblen_zero o
/-
**Ordinal.gamma_zero_eq_nfp** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：gamma_zero_eq_nfp : Γ₀ = nfp (veblen · 0) 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.deriv_zero_right`：deriv_zero_right (f) : deriv f 0 = nfp f 0
-/
theorem gamma_zero_eq_nfp : Γ₀ = nfp (veblen · 0) 0 :=
  deriv_zero_right _

@[deprecated (since := "2026-02-02")]
alias gamma0_eq_nfp := gamma_zero_eq_nfp
/-
**Ordinal.gamma_succ_eq_nfp** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：gamma_succ_eq_nfp (o : Ordinal) : Γ_ (succ o) = nfp (veblen · 0) (succ (Γ_
 o))
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.deriv_succ`：deriv_succ (f o) : deriv f (succ o) = nfp f (succ (d
eriv f o))
-/
theorem gamma_succ_eq_nfp (o : Ordinal) : Γ_ (succ o) = nfp (veblen · 0) (succ (Γ_ o)) :=
  deriv_succ _ _
/-
**Ordinal.gamma_zero_le_of_veblen_le** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：gamma_zero_le_of_veblen_le (h : veblen o 0 <= o) : Γ₀ <= o
参数：h : veblen o 0 <= o。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.gamma_zero_eq_nfp`：gamma_zero_eq_nfp : Γ₀ = nfp (veblen · 0) 0
· 使用定理 `Ordinal.nfp_le_fp`：nfp_le_fp (H : Monotone f) {a b} (ab : a <= b) (h : f
 b <= b) : nfp f a <= b
· 使用定理 `Ordinal.veblen_left_monotone`：veblen_left_monotone (o : Ordinal) : Monot
one (veblen · o)
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
-/
theorem gamma_zero_le_of_veblen_le (h : veblen o 0 ≤ o) : Γ₀ ≤ o := by
  rw [gamma_zero_eq_nfp]
  exact nfp_le_fp (veblen_left_monotone 0) zero_le h

@[deprecated (since := "2026-02-02")]
alias gamma0_le_of_veblen_le := gamma_zero_le_of_veblen_le

/-- `Γ₀` is the limit of `0`, `veblen 0 0`, `veblen (veblen 0 0) 0`, … -/
/-
**Ordinal.lt_gamma_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lt_gamma_zero : o < Γ₀ ↔ exists n : Nat, o < (fun a => veblen a 0)^[n] 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.gamma_zero_eq_nfp`：gamma_zero_eq_nfp : Γ₀ = nfp (veblen · 0) 0
· 使用定理 `Ordinal.lt_nfp_iff`：lt_nfp_iff {a b} : a < nfp f b ↔ exists n, a < f^[n]
 b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
`Γ₀` is the limit of `0`, `veblen 0 0`, `veblen (veblen 0 0) 0`, …
-/
theorem lt_gamma_zero : o < Γ₀ ↔ ∃ n : ℕ, o < (fun a ↦ veblen a 0)^[n] 0 := by
  rw [gamma_zero_eq_nfp, lt_nfp_iff]

@[deprecated (since := "2026-02-02")]
alias lt_gamma0 := lt_gamma_zero

/-- `veblen (veblen … (veblen 0 0) … 0) 0 < Γ₀` -/
/-
**Ordinal.iterate_veblen_lt_gamma_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：iterate_veblen_lt_gamma_zero (n : Nat) : (fun a => veblen a 0)^[n] 0 < Γ₀
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.gamma_zero_eq_nfp`：gamma_zero_eq_nfp : Γ₀ = nfp (veblen · 0) 0
· 使用定理 `Ordinal.iterate_lt_nfp`：iterate_lt_nfp (hf : StrictMono f) {a} (h : a < 
f a) (n : Nat) : f^[n] a < nfp f a
· 使用定理 `Ordinal.veblen_zero_strictMono`：veblen_zero_strictMono : StrictMono (veb
len · 0)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Ordinal.veblen_zero`：veblen_zero : veblen 0 = fun a => ω ^ a
· 使用定理 `Ordinal.opow_zero`：opow_zero (a : Ordinal) : a ^ (0 : Ordinal) = 1
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`veblen (veblen … (veblen 0 0) … 0) 0 < Γ₀`
-/
theorem iterate_veblen_lt_gamma_zero (n : ℕ) : (fun a ↦ veblen a 0)^[n] 0 < Γ₀ := by
  rw [gamma_zero_eq_nfp]
  apply iterate_lt_nfp veblen_zero_strictMono
  simp

@[deprecated (since := "2026-02-02")]
alias iterate_veblen_lt_gamma0 := iterate_veblen_lt_gamma_zero
/-
**Ordinal.epsilon_zero_lt_gamma** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：epsilon_zero_lt_gamma (o : Ordinal) : ε₀ < Γ_ o
参数：o : Ordinal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b ≤ a
 → c < b → c < a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ordinal.gamma_le_gamma`：gamma_le_gamma : Γ_ a <= Γ_ b ↔ a <= b
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Function.iterate_one`：iterate_one : f^[1] = f
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Ordinal.veblen_zero`：veblen_zero : veblen 0 = fun a => ω ^ a
· 使用定理 `Ordinal.opow_zero`：opow_zero (a : Ordinal) : a ^ (0 : Ordinal) = 1
· 使用定理 `Ordinal.iterate_veblen_lt_gamma_zero`：iterate_veblen_lt_gamma_zero (n : 
Nat) : (fun a => veblen a 0)^[n] 0 < Γ₀
-/
theorem epsilon_zero_lt_gamma (o : Ordinal) : ε₀ < Γ_ o := by
  apply (gamma_le_gamma.2 zero_le).trans_lt'
  simpa using iterate_veblen_lt_gamma_zero 2

@[deprecated (since := "2026-02-02")]
alias epsilon0_lt_gamma := epsilon_zero_lt_gamma
/-
**Ordinal.omega0_lt_gamma** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：omega0_lt_gamma (o : Ordinal) : ω < Γ_ o
参数：o : Ordinal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Ordinal.omega0_lt_epsilon`：omega0_lt_epsilon (o : Ordinal) : ω < ε_ o
· 使用定理 `Ordinal.epsilon_zero_lt_gamma`：epsilon_zero_lt_gamma (o : Ordinal) : ε₀ 
< Γ_ o
-/
theorem omega0_lt_gamma (o : Ordinal) : ω < Γ_ o :=
  (omega0_lt_epsilon 0).trans (epsilon_zero_lt_gamma o)
/-
**Ordinal.natCast_lt_gamma** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：natCast_lt_gamma (n : Nat) : n < Γ_ o
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Ordinal.natCast_lt_omega0`：natCast_lt_omega0 (n : Nat) : ↑n < ω
· 使用定理 `Ordinal.omega0_lt_gamma`：omega0_lt_gamma (o : Ordinal) : ω < Γ_ o
-/
theorem natCast_lt_gamma (n : ℕ) : n < Γ_ o :=
  (natCast_lt_omega0 n).trans (omega0_lt_gamma o)

@[simp]
/-
**Ordinal.gamma_pos** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：gamma_pos : 0 < Γ_ o
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.natCast_lt_gamma`：natCast_lt_gamma (n : Nat) : n < Γ_ o
-/
theorem gamma_pos : 0 < Γ_ o :=
  natCast_lt_gamma 0

@[simp]
/-
**Ordinal.gamma_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：gamma_ne_zero : Γ_ o != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Ordinal.gamma_pos`：gamma_pos : 0 < Γ_ o
-/
theorem gamma_ne_zero : Γ_ o ≠ 0 :=
  gamma_pos.ne'

@[simp]
/-
**Ordinal.invVeblen** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem invVeblen₁_gamma (o : Ordinal) : invVeblen₁ (Γ_ o) = Γ_ o := by
  rw [← veblen_gamma_zero, invVeblen₁_veblen veblen_pos, veblen_gamma_zero]

@[simp]
/-
**Ordinal.invVeblen** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem invVeblen₂_gamma (o : Ordinal) : invVeblen₂ (Γ_ o) = 0 := by
  rw [← veblen_gamma_zero, invVeblen₂_veblen gamma_ne_zero veblen_pos]
/-
**Ordinal.invVeblen** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem invVeblen₁_eq_iff : invVeblen₁ o = o ↔ o = 0 ∨ o ∈ range Γ_ := by
  constructor
  · rw [mem_range_gamma, or_iff_not_imp_left]
    refine fun h ho ↦ (left_le_veblen ..).antisymm' ?_
    conv_rhs => rw [← veblen_eq_of_lt_invVeblen₁ (h.trans_ne ho).bot_lt, bot_eq_zero,
      veblen_zero_apply, ← veblen_invVeblen₁_invVeblen₂, h]
    simp
  · aesop
/-
**Ordinal.invVeblen** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem invVeblen₁_lt_iff : invVeblen₁ o < o ↔ o ≠ 0 ∧ o ∉ range Γ_ := by
  rw [(invVeblen₁_le o).lt_iff_ne, ne_eq, invVeblen₁_eq_iff, not_or]

end Ordinal

