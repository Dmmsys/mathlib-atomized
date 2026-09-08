/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Combinatorics.SetFamily.Shadow

/-!
# UV-compressions

This file defines UV-compression. It is an operation on a set family that reduces its shadow.

UV-compressing `a : α` along `u v : α` means replacing `a` by `(a ⊔ u) \ v` if `a` and `u` are
disjoint and `v ≤ a`. In some sense, it's moving `a` from `v` to `u`.

UV-compressions are immensely useful to prove the Kruskal-Katona theorem. The idea is that
compressing a set family might decrease the size of its shadow, so iterated compressions hopefully
minimise the shadow.

## Main declarations

* `UV.compress`: `compress u v a` is `a` compressed along `u` and `v`.
* `UV.compression`: `compression u v s` is the compression of the set family `s` along `u` and `v`.
  It is the compressions of the elements of `s` whose compression is not already in `s` along with
  the element whose compression is already in `s`. This way of splitting into what moves and what
  does not ensures the compression doesn't squash the set family, which is proved by
  `UV.card_compression`.
* `UV.card_shadow_compression_le`: Compressing reduces the size of the shadow. This is a key fact in
  the proof of Kruskal-Katona.

## Notation

`𝓒` (typed with `\MCC`) is notation for `UV.compression` in scope `FinsetFamily`.

## Notes

Even though our emphasis is on `Finset α`, we define UV-compressions more generally in a generalized
Boolean algebra, so that one can use it for `Set α`.

## References

* https://github.com/b-mehta/maths-notes/blob/master/iii/mich/combinatorics.pdf

## Tags

compression, UV-compression, shadow
-/

@[expose] public section


open Finset

variable {α : Type*}

/-- UV-compression is injective on the elements it moves. See `UV.compress`. -/
/-
**sup_sdiff_injOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_sdiff_injOn [GeneralizedBooleanAlgebra α] (u v : α) : { x | Disjoint u
 x ∧ v <= x }.InjOn fun x => (x ⊔ u) \ v
参数：u v : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sdiff_sup_cancel`：sdiff_sup_cancel (h : b <= a) : a \ b ⊔ b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Disjoint.sup_sdiff_cancel_right`：∀ {α : Type u_2} [inst : GeneralizedCoh
eytingAlgebra α] {a b : α}, Disjoint a b → (a ⊔ b) \ b = a
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `sdiff_sdiff_comm`：sdiff_sdiff_comm : (a \ b) \ c = (a \ c) \ b

--- 原说明 ---
UV-compression is injective on the elements it moves. See `UV.compress`.
-/
theorem sup_sdiff_injOn [GeneralizedBooleanAlgebra α] (u v : α) :
    { x | Disjoint u x ∧ v ≤ x }.InjOn fun x => (x ⊔ u) \ v := by
  rintro a ha b hb hab
  have h : ((a ⊔ u) \ v) \ u ⊔ v = ((b ⊔ u) \ v) \ u ⊔ v := by
    dsimp at hab
    rw [hab]
  rwa [sdiff_sdiff_comm, ha.1.symm.sup_sdiff_cancel_right, sdiff_sdiff_comm,
    hb.1.symm.sup_sdiff_cancel_right, sdiff_sup_cancel ha.2, sdiff_sup_cancel hb.2] at h

-- The namespace is here to distinguish from other compressions.
namespace UV

/-! ### UV-compression in generalized Boolean algebras -/


section GeneralizedBooleanAlgebra

variable [GeneralizedBooleanAlgebra α] [DecidableRel (@Disjoint α _ _)]
  [DecidableLE α] {s : Finset α} {u v a : α}

/-- UV-compressing `a` means removing `v` from it and adding `u` if `a` and `u` are disjoint and
`v ≤ a` (it replaces the `v` part of `a` by the `u` part). Else, UV-compressing `a` doesn't do
anything. This is most useful when `u` and `v` are disjoint finsets of the same size. -/
/-
**UV.compress** 是 Mathlib 中的一个定义，位于命名空间 `UV`。
形式化陈述：compress (u v a : α) : α
参数：u v a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
UV-compressing `a` means removing `v` from it and adding `u` if `a` and `u` are 
disjoint and
`v ≤ a` (it replaces the `v` part of `a` by the `u` part). Else, UV-compressing 
`a` doesn't do
anything. This is most useful when `u` and `v` are disjoint finsets of the same 
size.
-/
def compress (u v a : α) : α :=
  if Disjoint u a ∧ v ≤ a then (a ⊔ u) \ v else a
/-
**UV.compress_of_disjoint_of_le** 是 Mathlib 中的一个定理，位于命名空间 `UV`。
形式化陈述：compress_of_disjoint_of_le (hua : Disjoint u a) (hva : v <= a) : compress 
u v a = (a ⊔ u) \ v
参数：hua : Disjoint u a；hva : v <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem compress_of_disjoint_of_le (hua : Disjoint u a) (hva : v ≤ a) :
    compress u v a = (a ⊔ u) \ v :=
  if_pos ⟨hua, hva⟩
/-
**UV.compress_of_disjoint_of_le'** 是 Mathlib 中的一个定理，位于命名空间 `UV`。
形式化陈述：compress_of_disjoint_of_le' (hva : Disjoint v a) (hua : u <= a) : compress
 u v ((a ⊔ v) \ u) = a
参数：hva : Disjoint v a；hua : u <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UV.compress_of_disjoint_of_le`：compress_of_disjoint_of_le (hua : Disjoin
t u a) (hva : v <= a) : compress u v a = (a ⊔ u) \ v
· 使用定理 `disjoint_sdiff_self_right`：disjoint_sdiff_self_right : Disjoint x (y \ x
)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `le_sdiff`：le_sdiff : x <= y \ z ↔ x <= y ∧ Disjoint x z
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `Disjoint.mono_right`：Disjoint.mono_right (h : b <= c) : Disjoint a c -> 
Disjoint a b
· 使用定理 `sdiff_sup_cancel`：sdiff_sup_cancel (h : b <= a) : a \ b ⊔ b = a
· 使用定理 `le_sup_of_le_left`：le_sup_of_le_left (h : c <= a) : c <= a ⊔ b
· 使用定理 `Disjoint.sup_sdiff_cancel_right`：∀ {α : Type u_2} [inst : GeneralizedCoh
eytingAlgebra α] {a b : α}, Disjoint a b → (a ⊔ b) \ b = a
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
-/
theorem compress_of_disjoint_of_le' (hva : Disjoint v a) (hua : u ≤ a) :
    compress u v ((a ⊔ v) \ u) = a := by
  rw [compress_of_disjoint_of_le disjoint_sdiff_self_right
      (le_sdiff.2 ⟨(le_sup_right : v ≤ a ⊔ v), hva.mono_right hua⟩),
    sdiff_sup_cancel (le_sup_of_le_left hua), hva.symm.sup_sdiff_cancel_right]

@[simp, grind =]
/-
**UV.compress_self** 是 Mathlib 中的一个定理，位于命名空间 `UV`。
形式化陈述：compress_self (u a : α) : compress u u a = a
参数：u a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Disjoint.sup_sdiff_cancel_right`：∀ {α : Type u_2} [inst : GeneralizedCoh
eytingAlgebra α] {a b : α}, Disjoint a b → (a ⊔ b) \ b = a
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem compress_self (u a : α) : compress u u a = a := by
  unfold compress
  split_ifs with h
  · exact h.1.symm.sup_sdiff_cancel_right
  · rfl

/-- An element can be compressed to any other element by removing/adding the differences. -/
@[simp]
/-
**UV.compress_sdiff_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `UV`。
形式化陈述：compress_sdiff_sdiff (a b : α) : compress (a \ b) (b \ a) b = a
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `UV.compress_of_disjoint_of_le`：compress_of_disjoint_of_le (hua : Disjoin
t u a) (hva : v <= a) : compress u v a = (a ⊔ u) \ v
· 使用定理 `disjoint_sdiff_self_left`：disjoint_sdiff_self_left : Disjoint (y \ x) x
· 使用定理 `sdiff_le`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a b :
 α}, a \ b ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_sdiff_self_right`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgeb
ra α] (a b : α), a ⊔ b \ a = a ⊔ b
· 使用定理 `sup_sdiff`：sup_sdiff : (a ⊔ b) \ c = a \ c ⊔ b \ c
· 使用定理 `Disjoint.sdiff_eq_left`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlg
ebra α] {a b : α}, Disjoint a b → a \ b = a
· 使用定理 `disjoint_sdiff_self_right`：disjoint_sdiff_self_right : Disjoint x (y \ x
)
· 使用定理 `sup_eq_right`：sup_eq_right : a ⊔ b = b ↔ a <= b
· 使用定理 `sdiff_sdiff_le`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] 
{a b : α}, b \ (b \ a) ≤ a

--- 原说明 ---
An element can be compressed to any other element by removing/adding the differe
nces.
-/
theorem compress_sdiff_sdiff (a b : α) : compress (a \ b) (b \ a) b = a := by
  refine (compress_of_disjoint_of_le disjoint_sdiff_self_left sdiff_le).trans ?_
  rw [sup_sdiff_self_right, sup_sdiff, disjoint_sdiff_self_right.sdiff_eq_left, sup_eq_right]
  exact sdiff_sdiff_le

/-- Compressing an element is idempotent. -/
@[simp]
/-
**UV.compress_idem** 是 Mathlib 中的一个定理，位于命名空间 `UV`。
形式化陈述：compress_idem (u v a : α) : compress u v (compress u v a) = compress u v a
参数：u v a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_sdiff_right`：le_sdiff_right : x <= y \ x ↔ x = ⊥
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `sdiff_bot`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a : 
α}, a \ ⊥ = a
· 使用定理 `sup_assoc`：sup_assoc (a b c : α) : a ⊔ b ⊔ c = a ⊔ (b ⊔ c)
· 使用定理 `sup_idem`：sup_idem (a : α) : a ⊔ a = a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c

--- 原说明 ---
Compressing an element is idempotent.
-/
theorem compress_idem (u v a : α) : compress u v (compress u v a) = compress u v a := by
  unfold compress
  split_ifs with h h'
  · rw [le_sdiff_right.1 h'.2, sdiff_bot, sdiff_bot, sup_assoc, sup_idem]
  · rfl
  · rfl

variable [DecidableEq α]

/-- To UV-compress a set family, we compress each of its elements, except that we don't want to
reduce the cardinality, so we keep all elements whose compression is already present. -/
/-
**UV.compression** 是 Mathlib 中的一个定义，位于命名空间 `UV`。
形式化陈述：compression (u v : α) (s : Finset α)
参数：u v : α；s : Finset α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
To UV-compress a set family, we compress each of its elements, except that we do
n't want to
reduce the cardinality, so we keep all elements whose compression is already pre
sent.
-/
def compression (u v : α) (s : Finset α) :=
  {a ∈ s | compress u v a ∈ s} ∪ {a ∈ s.image <| compress u v | a ∉ s}

@[inherit_doc]
scoped[FinsetFamily] notation "𝓒 " => UV.compression

open scoped FinsetFamily

/-- `IsCompressed u v s` expresses that `s` is UV-compressed. -/
/-
**UV.IsCompressed** 是 Mathlib 中的一个定义，位于命名空间 `UV`。
形式化陈述：IsCompressed (u v : α) (s : Finset α)
参数：u v : α；s : Finset α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsCompressed u v s` expresses that `s` is UV-compressed.
-/
def IsCompressed (u v : α) (s : Finset α) :=
  𝓒 u v s = s

/-- UV-compression is injective on the sets that are not UV-compressed. -/
/-
**UV.compress_injOn** 是 Mathlib 中的一个定理，位于命名空间 `UV`。
形式化陈述：compress_injOn : Set.InjOn (compress u v) ↑{a in s | compress u v a ∉ s}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_sdiff_injOn`：sup_sdiff_injOn [GeneralizedBooleanAlgebra α] (u v : α)
 : { x | Disjoint u x ∧ v <= x }.InjOn fun x => (x ⊔ u) \ v
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `UV.compress.eq_1`：∀ {α : Type u_1} [inst : GeneralizedBooleanAlgebra α] 
[inst_1 : DecidableRel Disjoint] [inst_2 : DecidableLE α]   (u v a : α), UV.comp
ress u…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `Finset.mem_coe`：mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in
 (s : Finset α)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
UV-compression is injective on the sets that are not UV-compressed.
-/
theorem compress_injOn : Set.InjOn (compress u v) ↑{a ∈ s | compress u v a ∉ s} := by
  intro a ha b hb hab
  rw [mem_coe, mem_filter] at ha hb
  rw [compress] at ha hab
  split_ifs at ha hab with has
  · rw [compress] at hb hab
    split_ifs at hb hab with hbs
    · exact sup_sdiff_injOn u v has hbs hab
    · exact (hb.2 hb.1).elim
  · exact (ha.2 ha.1).elim

/-- `a` is in the UV-compressed family iff it's in the original and its compression is in the
original, or it's not in the original but it's the compression of something in the original. -/
/-
**UV.mem_compression** 是 Mathlib 中的一个定理，位于命名空间 `UV`。
形式化陈述：mem_compression : a in 𝓒 u v s ↔ a in s ∧ compress u v a in s ∨ a ∉ s ∧ ex
ists b in s, compress u v b = a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
`a` is in the UV-compressed family iff it's in the original and its compression 
is in the
original, or it's not in the original but it's the compression of something in t
he original.
-/
theorem mem_compression :
    a ∈ 𝓒 u v s ↔ a ∈ s ∧ compress u v a ∈ s ∨ a ∉ s ∧ ∃ b ∈ s, compress u v b = a := by
  simp_rw [compression, mem_union, mem_filter, mem_image, and_comm]
/-
**UV.IsCompressed.eq** 是 Mathlib 中的一个定理，位于命名空间 `UV.IsCompressed`。
形式化陈述：∀ {α : Type u_1} [inst : GeneralizedBooleanAlgebra α] [inst_1 : DecidableR
el Disjoint] [inst_2 : DecidableLE α]   {s : Finset α} {u v : α} [inst_3 : Decid
ableEq α], UV.IsCompressed u v s → UV.compression u v s = s
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem IsCompressed.eq (h : IsCompressed u v s) : 𝓒 u v s = s := h

@[simp]
/-
**UV.compression_self** 是 Mathlib 中的一个定理，位于命名空间 `UV`。
形式化陈述：compression_self (u : α) (s : Finset α) : 𝓒 u u s = s
参数：u : α；s : Finset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem compression_self (u : α) (s : Finset α) : 𝓒 u u s = s := by
  grind [mem_compression]

/-- Any family is compressed along two identical elements. -/
/-
**UV.isCompressed_self** 是 Mathlib 中的一个定理，位于命名空间 `UV`。
形式化陈述：isCompressed_self (u : α) (s : Finset α) : IsCompressed u u s
参数：u : α；s : Finset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UV.compression_self`：compression_self (u : α) (s : Finset α) : 𝓒 u u s =
 s

--- 原说明 ---
Any family is compressed along two identical elements.
-/
theorem isCompressed_self (u : α) (s : Finset α) : IsCompressed u u s := compression_self u s
/-
**UV.compress_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `UV`。
形式化陈述：compress_disjoint : Disjoint {a in s | compress u v a in s} {a in s.image 
<| compress u v | a ∉ s}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s 
-> a ∉ t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem compress_disjoint :
    Disjoint {a ∈ s | compress u v a ∈ s} {a ∈ s.image <| compress u v | a ∉ s} :=
  disjoint_left.2 fun _a ha₁ ha₂ ↦ (mem_filter.1 ha₂).2 (mem_filter.1 ha₁).1
/-
**UV.compress_mem_compression** 是 Mathlib 中的一个定理，位于命名空间 `UV`。
形式化陈述：compress_mem_compression (ha : a in s) : compress u v a in 𝓒 u v s
参数：ha : a in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UV.mem_compression`：mem_compression : a in 𝓒 u v s ↔ a in s ∧ compress u
 v a in s ∨ a ∉ s ∧ exists b in s, compress u v b = a
· 使用定理 `UV.compress_idem`：compress_idem (u v a : α) : compress u v (compress u v
 a) = compress u v a
-/
theorem compress_mem_compression (ha : a ∈ s) : compress u v a ∈ 𝓒 u v s := by
  rw [mem_compression]
  by_cases h : compress u v a ∈ s
  · rw [compress_idem]
    exact Or.inl ⟨h, h⟩
  · exact Or.inr ⟨h, a, ha, rfl⟩

-- This is a special case of `compress_mem_compression` once we have `compression_idem`.
/-
**UV.compress_mem_compression_of_mem_compression** 是 Mathlib 中的一个定理，位于命名空间 `UV`。
形式化陈述：compress_mem_compression_of_mem_compression (ha : a in 𝓒 u v s) : compress
 u v a in 𝓒 u v s
参数：ha : a in 𝓒 u v s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UV.mem_compression`：mem_compression : a in 𝓒 u v s ↔ a in s ∧ compress u
 v a in s ∨ a ∉ s ∧ exists b in s, compress u v b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `UV.compress_idem`：compress_idem (u v a : α) : compress u v (compress u v
 a) = compress u v a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem compress_mem_compression_of_mem_compression (ha : a ∈ 𝓒 u v s) :
    compress u v a ∈ 𝓒 u v s := by
  rw [mem_compression] at ha ⊢
  simp only [compress_idem]
  obtain ⟨_, ha⟩ | ⟨_, b, hb, rfl⟩ := ha
  · exact Or.inl ⟨ha, ha⟩
  · exact Or.inr ⟨by rwa [compress_idem], b, hb, (compress_idem _ _ _).symm⟩

/-- Compressing a family is idempotent. -/
@[simp]
/-
**UV.compression_idem** 是 Mathlib 中的一个定理，位于命名空间 `UV`。
形式化陈述：compression_idem (u v : α) (s : Finset α) : 𝓒 u v (𝓒 u v s) = 𝓒 u v s
参数：u v : α；s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.filter_false_of_mem`：∀ {α : Type u_1} {p : α → Prop} [inst : Deci
dablePred p] {s : Finset α}, (∀ x ∈ s, ¬p x) → Finset.filter p s = ∅
· 使用定理 `UV.compress_mem_compression_of_mem_compression`：compress_mem_compression
_of_mem_compression (ha : a in 𝓒 u v s) : compress u v a in 𝓒 u v s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UV.compression.eq_1`：∀ {α : Type u_1} [inst : GeneralizedBooleanAlgebra 
α] [inst_1 : DecidableRel Disjoint] [inst_2 : DecidableLE α]   [inst_3 : Decidab
leEq α] (…
· 使用定理 `Finset.filter_image`：filter_image {p : β -> Prop} [DecidablePred p] : (s
.image f).filter p = (s.filter fun a => p (f a)).image f
· 使用定理 `Finset.image_empty`：image_empty (f : α -> β) : (∅ : Finset α).image f = 
∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.filter_union_filter_not_eq`：filter_union_filter_not_eq [forall x,
 Decidable (¬p x)] (s : Finset α) : (s.filter p union s.filter fun a => ¬p a) = 
s

--- 原说明 ---
Compressing a family is idempotent.
-/
theorem compression_idem (u v : α) (s : Finset α) : 𝓒 u v (𝓒 u v s) = 𝓒 u v s := by
  have h : {a ∈ 𝓒 u v s | compress u v a ∉ 𝓒 u v s} = ∅ :=
    filter_false_of_mem fun a ha h ↦ h <| compress_mem_compression_of_mem_compression ha
  rw [compression, filter_image, h, image_empty, ← h]
  exact filter_union_filter_not_eq _ (compression u v s)

/-- Compressing a family doesn't change its size. -/
@[simp]
/-
**UV.card_compression** 是 Mathlib 中的一个定理，位于命名空间 `UV`。
形式化陈述：card_compression (u v : α) (s : Finset α) : #(𝓒 u v s) = #s
参数：u v : α；s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UV.compression.eq_1`：∀ {α : Type u_1} [inst : GeneralizedBooleanAlgebra 
α] [inst_1 : DecidableRel Disjoint] [inst_2 : DecidableLE α]   [inst_3 : Decidab
leEq α] (…
· 使用定理 `Finset.card_union_of_disjoint`：∀ {α : Type u_1} {s t : Finset α} [inst :
 DecidableEq α], Disjoint s t → (s ∪ t).card = s.card + t.card
· 使用定理 `UV.compress_disjoint`：compress_disjoint : Disjoint {a in s | compress u 
v a in s} {a in s.image <| compress u v | a ∉ s}
· 使用定理 `Finset.filter_image`：filter_image {p : β -> Prop} [DecidablePred p] : (s
.image f).filter p = (s.filter fun a => p (f a)).image f
· 使用定理 `Finset.card_image_of_injOn`：card_image_of_injOn [DecidableEq β] (H : Set
.InjOn f s) : #(s.image f) = #s
· 使用定理 `UV.compress_injOn`：compress_injOn : Set.InjOn (compress u v) ↑{a in s | 
compress u v a ∉ s}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.disjoint_filter_filter_not`：disjoint_filter_filter_not (s t : Fin
set α) (p : α -> Prop) [DecidablePred p] [forall x, Decidable (¬p x)] : Disjoint
 (s.filter p) (t.filter…
· 使用定理 `Finset.filter_union_filter_not_eq`：filter_union_filter_not_eq [forall x,
 Decidable (¬p x)] (s : Finset α) : (s.filter p union s.filter fun a => ¬p a) = 
s

--- 原说明 ---
Compressing a family doesn't change its size.
-/
theorem card_compression (u v : α) (s : Finset α) : #(𝓒 u v s) = #s := by
  rw [compression, card_union_of_disjoint compress_disjoint, filter_image,
    card_image_of_injOn compress_injOn, ← card_union_of_disjoint (disjoint_filter_filter_not s _ _),
    filter_union_filter_not_eq]
/-
**UV.le_of_mem_compression_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `UV`。
形式化陈述：le_of_mem_compression_of_notMem (h : a in 𝓒 u v s) (ha : a ∉ s) : u <= a
参数：h : a in 𝓒 u v s；ha : a ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UV.mem_compression`：mem_compression : a in 𝓒 u v s ↔ a in s ∧ compress u
 v a in s ∨ a ∉ s ∧ exists b in s, compress u v b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用引理 `le_sdiff`：le_sdiff : x <= y \ z ↔ x <= y ∧ Disjoint x z
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `Disjoint.mono_right`：Disjoint.mono_right (h : b <= c) : Disjoint a c -> 
Disjoint a b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem le_of_mem_compression_of_notMem (h : a ∈ 𝓒 u v s) (ha : a ∉ s) : u ≤ a := by
  rw [mem_compression] at h
  obtain h | ⟨-, b, hb, hba⟩ := h
  · cases ha h.1
  unfold compress at hba
  split_ifs at hba with h
  · rw [← hba, le_sdiff]
    exact ⟨le_sup_right, h.1.mono_right h.2⟩
  · cases ne_of_mem_of_not_mem hb ha hba
/-
**UV.disjoint_of_mem_compression_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `UV`。
形式化陈述：disjoint_of_mem_compression_of_notMem (h : a in 𝓒 u v s) (ha : a ∉ s) : Di
sjoint v a
参数：h : a in 𝓒 u v s；ha : a ∉ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UV.mem_compression`：mem_compression : a in 𝓒 u v s ↔ a in s ∧ compress u
 v a in s ∨ a ∉ s ∧ exists b in s, compress u v b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `disjoint_sdiff_self_right`：disjoint_sdiff_self_right : Disjoint x (y \ x
)
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem disjoint_of_mem_compression_of_notMem (h : a ∈ 𝓒 u v s) (ha : a ∉ s) : Disjoint v a := by
  rw [mem_compression] at h
  obtain h | ⟨-, b, hb, hba⟩ := h
  · cases ha h.1
  unfold compress at hba
  split_ifs at hba
  · rw [← hba]
    exact disjoint_sdiff_self_right
  · cases ne_of_mem_of_not_mem hb ha hba
/-
**UV.sup_sdiff_mem_of_mem_compression_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `UV`。
形式化陈述：sup_sdiff_mem_of_mem_compression_of_notMem (h : a in 𝓒 u v s) (ha : a ∉ s)
 : (a ⊔ v) \ u in s
参数：h : a in 𝓒 u v s；ha : a ∉ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UV.mem_compression`：mem_compression : a in 𝓒 u v s ↔ a in s ∧ compress u
 v a in s ∨ a ∉ s ∧ exists b in s, compress u v b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `sdiff_sup_cancel`：sdiff_sup_cancel (h : b <= a) : a \ b ⊔ b = a
· 使用定理 `le_sup_of_le_left`：le_sup_of_le_left (h : c <= a) : c <= a ⊔ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `sup_sdiff_right_self`：sup_sdiff_right_self : (a ⊔ b) \ b = a \ b
· 使用定理 `Disjoint.sdiff_eq_left`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlg
ebra α] {a b : α}, Disjoint a b → a \ b = a
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem sup_sdiff_mem_of_mem_compression_of_notMem (h : a ∈ 𝓒 u v s) (ha : a ∉ s) :
    (a ⊔ v) \ u ∈ s := by
  rw [mem_compression] at h
  obtain h | ⟨-, b, hb, hba⟩ := h
  · cases ha h.1
  unfold compress at hba
  split_ifs at hba with h
  · rwa [← hba, sdiff_sup_cancel (le_sup_of_le_left h.2), sup_sdiff_right_self,
      h.1.symm.sdiff_eq_left]
  · cases ne_of_mem_of_not_mem hb ha hba

/-- If `a` is in the family compression and can be compressed, then its compression is in the
original family. -/
/-
**UV.sup_sdiff_mem_of_mem_compression** 是 Mathlib 中的一个定理，位于命名空间 `UV`。
形式化陈述：sup_sdiff_mem_of_mem_compression (ha : a in 𝓒 u v s) (hva : v <= a) (hua :
 Disjoint u a) : (a ⊔ u) \ v in s
参数：ha : a in 𝓒 u v s；hva : v <= a；hua : Disjoint u a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UV.compress_of_disjoint_of_le`：compress_of_disjoint_of_le (hua : Disjoin
t u a) (hva : v <= a) : compress u v a = (a ⊔ u) \ v
· 使用定理 `UV.mem_compression`：mem_compression : a in 𝓒 u v s ↔ a in s ∧ compress u
 v a in s ∨ a ∉ s ∧ exists b in s, compress u v b = a
· 使用定理 `Disjoint.mono_right`：Disjoint.mono_right (h : b <= c) : Disjoint a c -> 
Disjoint a b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `UV.compress_idem`：compress_idem (u v a : α) : compress u v (compress u v
 a) = compress u v a
· 使用定理 `sdiff_le_sdiff_right`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgeb
ra α] {a b c : α}, b ≤ a → b \ c ≤ a \ c
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `disjoint_self`：disjoint_self : Disjoint a a ↔ a = ⊥
· 使用定理 `Disjoint.sdiff_eq_left`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlg
ebra α] {a b : α}, Disjoint a b → a \ b = a
· 使用定理 `disjoint_sdiff_self_right`：disjoint_sdiff_self_right : Disjoint x (y \ x
)
· 使用定理 `UV.compress_self`：compress_self (u a : α) : compress u u a = a
· 使用定理 `sup_bot_eq`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : OrderBo
t α] (a : α), a ⊔ ⊥ = a
· 使用定理 `sdiff_bot`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a : 
α}, a \ ⊥ = a

--- 原说明 ---
If `a` is in the family compression and can be compressed, then its compression 
is in the
original family.
-/
theorem sup_sdiff_mem_of_mem_compression (ha : a ∈ 𝓒 u v s) (hva : v ≤ a) (hua : Disjoint u a) :
    (a ⊔ u) \ v ∈ s := by
  rw [mem_compression, compress_of_disjoint_of_le hua hva] at ha
  obtain ⟨_, ha⟩ | ⟨_, b, hb, rfl⟩ := ha
  · exact ha
  have hu : u = ⊥ := by
    suffices Disjoint u (u \ v) by rwa [(hua.mono_right hva).sdiff_eq_left, disjoint_self] at this
    refine hua.mono_right ?_
    rw [← compress_idem, compress_of_disjoint_of_le hua hva]
    exact sdiff_le_sdiff_right le_sup_right
  have hv : v = ⊥ := by
    rw [← disjoint_self]
    apply Disjoint.mono_right hva
    rw [← compress_idem, compress_of_disjoint_of_le hua hva]
    exact disjoint_sdiff_self_right
  rwa [hu, hv, compress_self, sup_bot_eq, sdiff_bot]

/-- If `a` is in the `u, v`-compression but `v ≤ a`, then `a` must have been in the original
family. -/
/-
**UV.mem_of_mem_compression** 是 Mathlib 中的一个定理，位于命名空间 `UV`。
形式化陈述：mem_of_mem_compression (ha : a in 𝓒 u v s) (hva : v <= a) (hvu : v = ⊥ -> 
u = ⊥) : a in s
参数：ha : a in 𝓒 u v s；hva : v <= a；hvu : v = ⊥ -> u = ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UV.mem_compression`：mem_compression : a in 𝓒 u v s ↔ a in s ∧ compress u
 v a in s ∨ a ∉ s ∧ exists b in s, compress u v b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `le_sdiff_right`：le_sdiff_right : x <= y \ x ↔ x = ⊥
· 使用定理 `sup_bot_eq`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : OrderBo
t α] (a : α), a ⊔ ⊥ = a
· 使用定理 `sdiff_bot`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a : 
α}, a \ ⊥ = a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e

--- 原说明 ---
If `a` is in the `u, v`-compression but `v ≤ a`, then `a` must have been in the 
original
family.
-/
theorem mem_of_mem_compression (ha : a ∈ 𝓒 u v s) (hva : v ≤ a) (hvu : v = ⊥ → u = ⊥) :
    a ∈ s := by
  rw [mem_compression] at ha
  obtain ha | ⟨_, b, hb, h⟩ := ha
  · exact ha.1
  unfold compress at h
  split_ifs at h
  · rw [← h, le_sdiff_right] at hva
    rwa [← h, hvu hva, hva, sup_bot_eq, sdiff_bot]
  · rwa [← h]

end GeneralizedBooleanAlgebra

/-! ### UV-compression on finsets -/

open FinsetFamily

variable [DecidableEq α] {𝒜 : Finset (Finset α)} {u v : Finset α} {r : ℕ}

/-- Compressing a finset doesn't change its size. -/
/-
**UV.card_compress** 是 Mathlib 中的一个定理，位于命名空间 `UV`。
形式化陈述：card_compress (huv : #u = #v) (a : Finset α) : #(compress u v a) = #a
参数：huv : #u = #v；a : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Finset.card_sdiff_of_subset`：card_sdiff_of_subset (h : s subseteq t) : #
(t \ s) = #t - #s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `Finset.sup_eq_union`：sup_eq_union {s t : Finset α} : s ⊔ t = s union t
· 使用定理 `Finset.card_union_of_disjoint`：∀ {α : Type u_1} {s t : Finset α} [inst :
 DecidableEq α], Disjoint s t → (s ∪ t).card = s.card + t.card
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e

--- 原说明 ---
Compressing a finset doesn't change its size.
-/
theorem card_compress (huv : #u = #v) (a : Finset α) : #(compress u v a) = #a := by
  unfold compress
  split_ifs with h
  · rw [card_sdiff_of_subset (h.2.trans le_sup_left), sup_eq_union,
      card_union_of_disjoint h.1.symm, huv, add_tsub_cancel_right]
  · rfl
/-
**UV._root_.Set.Sized.uvCompression** 是 Mathlib 中的一个引理，位于命名空间 `UV`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Set.Sized.uvCompression (huv : #u = #v) (h𝒜 : (𝒜 : Set (Finset α)).Sized r) :
    (𝓒 u v 𝒜 : Set (Finset α)).Sized r := by
  simp_rw [Set.Sized, mem_coe, mem_compression]
  rintro s (hs | ⟨huvt, t, ht, rfl⟩)
  · exact h𝒜 hs.1
  · rw [card_compress huv, h𝒜 ht]
/-
**UV.aux** 是 Mathlib 中的一个定理，位于命名空间 `UV`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem aux (huv : ∀ x ∈ u, ∃ y ∈ v, IsCompressed (u.erase x) (v.erase y) 𝒜) :
    v = ∅ → u = ∅ := by
  grind

/-- UV-compression reduces the size of the shadow of `𝒜` if, for all `x ∈ u` there is `y ∈ v` such
that `𝒜` is `(u.erase x, v.erase y)`-compressed. This is the key fact about compression for
Kruskal-Katona. -/
/-
**UV.shadow_compression_subset_compression_shadow** 是 Mathlib 中的一个定理，位于命名空间 `UV`
。
形式化陈述：shadow_compression_subset_compression_shadow (u v : Finset α) (huv : foral
l x in u, exists y in v, IsCompressed (u.erase x) (v.erase y) 𝒜) : ∂ (𝓒 u v 𝒜) s
ubseteq 𝓒 u v (∂ 𝒜)
参数：u v : Finset α；huv : forall x in u, exists y in v, IsCompressed (u.erase x) (
v.erase y) 𝒜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Finset.mem_shadow_iff_insert_mem`：mem_shadow_iff_insert_mem : t in ∂ 𝒜 ↔
 exists a ∉ t, insert a t in 𝒜
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `UV.le_of_mem_compression_of_notMem`：le_of_mem_compression_of_notMem (h :
 a in 𝓒 u v s) (ha : a ∉ s) : u <= a
· 使用定理 `UV.disjoint_of_mem_compression_of_notMem`：disjoint_of_mem_compression_of
_notMem (h : a in 𝓒 u v s) (ha : a ∉ s) : Disjoint v a
· 使用定理 `UV.sup_sdiff_mem_of_mem_compression_of_notMem`：sup_sdiff_mem_of_mem_comp
ression_of_notMem (h : a in 𝓒 u v s) (ha : a ∉ s) : (a ⊔ v) \ u in s
· 使用定理 `Disjoint.mono_left`：Disjoint.mono_left (h : a <= b) : Disjoint b c -> Di
sjoint a c
· 使用定理 `Finset.subset_insert`：∀ {α : Type u_1} [inst : DecidableEq α] (a : α) (s
 : Finset α), s ⊆ insert a s
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `Finset.disjoint_of_subset_right`：disjoint_of_subset_right (h : t subsete
q u) (d : Disjoint s u) : Disjoint s t
· 使用定理 `Finset.disjoint_right`：disjoint_right : Disjoint s t ↔ forall ⦃a⦄, a in 
t -> a ∉ s
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `Disjoint.sdiff_eq_left`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlg
ebra α] {a b : α}, Disjoint a b → a \ b = a
· 使用定理 `UV.sup_sdiff_mem_of_mem_compression`：sup_sdiff_mem_of_mem_compression (h
a : a in 𝓒 u v s) (hva : v <= a) (hua : Disjoint u a) : (a ⊔ u) \ v in s
· 使用定理 `UV.IsCompressed.eq`：∀ {α : Type u_1} [inst : GeneralizedBooleanAlgebra α
] [inst_1 : DecidableRel Disjoint] [inst_2 : DecidableLE α]   {s : Finset α} {u 
v : α} […
· 使用定理 `Finset.union_sdiff_distrib`：union_sdiff_distrib (s₁ s₂ t : Finset α) : (
s₁ union s₂) \ t = s₁ \ t union s₂ \ t
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.erase_subset`：erase_subset (a : α) (s : Finset α) : erase s a sub
seteq s
· 使用定理 `Finset.subset_union_right`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s
₂ : Finset α}, s₂ ⊆ s₁ ∪ s₂
· 使用定理 `Finset.disjoint_of_subset_left`：disjoint_of_subset_left (h : s subseteq 
u) (d : Disjoint u t) : Disjoint s t
· 使用定理 `Finset.disjoint_sdiff`：disjoint_sdiff : Disjoint s (t \ s)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sdiff_union_erase_cancel`：sdiff_union_erase_cancel (hts : t subse
teq s) (ha : a in t) : s \ t union t.erase a = s.erase a
· 使用定理 `Finset.subset_union_left`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s₂
 : Finset α}, s₁ ⊆ s₁ ∪ s₂
· 使用定理 `Finset.erase_union_distrib`：erase_union_distrib (s t : Finset α) (a : α)
 : (s union t).erase a = s.erase a union t.erase a
· 使用定理 `Finset.erase_insert`：erase_insert {a : α} {s : Finset α} (h : a ∉ s) : (
insert a s).erase a = s
· 使用定理 `Finset.erase_eq_of_notMem`：erase_eq_of_notMem {a : α} {s : Finset α} (h 
: a ∉ s) : erase s a = s
· 使用定理 `Finset.sdiff_erase`：sdiff_erase (h : a in s) : s \ t.erase a = insert a 
(s \ t)
（共 70 条，此处仅展示前 30 条）

--- 原说明 ---
UV-compression reduces the size of the shadow of `𝒜` if, for all `x ∈ u` there i
s `y ∈ v` such
that `𝒜` is `(u.erase x, v.erase y)`-compressed. This is the key fact about comp
ression for
Kruskal-Katona.
-/
theorem shadow_compression_subset_compression_shadow (u v : Finset α)
    (huv : ∀ x ∈ u, ∃ y ∈ v, IsCompressed (u.erase x) (v.erase y) 𝒜) :
    ∂ (𝓒 u v 𝒜) ⊆ 𝓒 u v (∂ 𝒜) := by
  set 𝒜' := 𝓒 u v 𝒜
  suffices H : ∀ s ∈ ∂ 𝒜',
      s ∉ ∂ 𝒜 → u ⊆ s ∧ Disjoint v s ∧ (s ∪ v) \ u ∈ ∂ 𝒜 ∧ (s ∪ v) \ u ∉ ∂ 𝒜' by
    rintro s hs'
    rw [mem_compression]
    by_cases hs : s ∈ 𝒜.shadow
    swap
    · obtain ⟨hus, hvs, h, _⟩ := H _ hs' hs
      exact Or.inr ⟨hs, _, h, compress_of_disjoint_of_le' hvs hus⟩
    refine Or.inl ⟨hs, ?_⟩
    rw [compress]
    split_ifs with huvs
    swap
    · exact hs
    rw [mem_shadow_iff] at hs'
    obtain ⟨t, Ht, a, hat, rfl⟩ := hs'
    have hav : a ∉ v := notMem_mono huvs.2 (notMem_erase a t)
    have hvt : v ≤ t := huvs.2.trans (erase_subset _ t)
    have ht : t ∈ 𝒜 := mem_of_mem_compression Ht hvt (aux huv)
    by_cases hau : a ∈ u
    · obtain ⟨b, hbv, Hcomp⟩ := huv a hau
      refine mem_shadow_iff_insert_mem.2 ⟨b, notMem_sdiff_of_mem_right hbv, ?_⟩
      rw [← Hcomp.eq] at ht
      have hsb :=
        sup_sdiff_mem_of_mem_compression ht ((erase_subset _ _).trans hvt)
          (disjoint_erase_comm.2 huvs.1)
      rwa [sup_eq_union, sdiff_erase (mem_union_left _ <| hvt hbv), union_erase_of_mem hat, ←
        erase_union_of_mem hau] at hsb
    · refine mem_shadow_iff.2
        ⟨(t ⊔ u) \ v,
          sup_sdiff_mem_of_mem_compression Ht hvt <| disjoint_of_erase_right hau huvs.1, a, ?_, ?_⟩
      · rw [sup_eq_union, mem_sdiff, mem_union]
        exact ⟨Or.inl hat, hav⟩
      · simp [← erase_sdiff_comm, erase_union_distrib, erase_eq_of_notMem hau]
  intro s hs𝒜' hs𝒜
  -- This is going to be useful a couple of times so let's name it.
  have m : ∀ y, y ∉ s → insert y s ∉ 𝒜 := fun y h a => hs𝒜 (mem_shadow_iff_insert_mem.2 ⟨y, h, a⟩)
  obtain ⟨x, _, _⟩ := mem_shadow_iff_insert_mem.1 hs𝒜'
  have hus : u ⊆ insert x s := le_of_mem_compression_of_notMem ‹_ ∈ 𝒜'› (m _ ‹x ∉ s›)
  have hvs : Disjoint v (insert x s) := disjoint_of_mem_compression_of_notMem ‹_› (m _ ‹x ∉ s›)
  have : (insert x s ∪ v) \ u ∈ 𝒜 := sup_sdiff_mem_of_mem_compression_of_notMem ‹_› (m _ ‹x ∉ s›)
  have hsv : Disjoint s v := hvs.symm.mono_left (subset_insert _ _)
  have hvu : Disjoint v u := disjoint_of_subset_right hus hvs
  have hxv : x ∉ v := disjoint_right.1 hvs (mem_insert_self _ _)
  have : v \ u = v := ‹Disjoint v u›.sdiff_eq_left
  -- The first key part is that `x ∉ u`
  have : x ∉ u := by
    intro hxu
    obtain ⟨y, hyv, hxy⟩ := huv x hxu
    -- If `x ∈ u`, we can get `y ∈ v` so that `𝒜` is `(u.erase x, v.erase y)`-compressed
    apply m y (disjoint_right.1 hsv hyv)
    -- and we will use this `y` to contradict `m`, so we would like to show `insert y s ∈ 𝒜`.
    -- We do this by showing the below
    have : ((insert x s ∪ v) \ u ∪ erase u x) \ erase v y ∈ 𝒜 := by
      refine
        sup_sdiff_mem_of_mem_compression (by rwa [hxy.eq]) ?_
          (disjoint_of_subset_left (erase_subset _ _) disjoint_sdiff)
      rw [union_sdiff_distrib, ‹v \ u = v›]
      exact (erase_subset _ _).trans subset_union_right
    -- and then arguing that it's the same
    convert! this using 1
    rw [sdiff_union_erase_cancel (hus.trans subset_union_left) ‹x ∈ u›, erase_union_distrib,
      erase_insert ‹x ∉ s›, erase_eq_of_notMem ‹x ∉ v›, sdiff_erase (mem_union_right _ hyv),
      union_sdiff_cancel_right hsv]
  -- Now that this is done, it's immediate that `u ⊆ s`
  have hus : u ⊆ s := by rwa [← erase_eq_of_notMem ‹x ∉ u›, ← subset_insert_iff]
  -- and we already had that `v` and `s` are disjoint,
  -- so it only remains to get `(s ∪ v) \ u ∈ ∂ 𝒜 \ ∂ 𝒜'`
  simp_rw [mem_shadow_iff_insert_mem]
  refine ⟨hus, hsv.symm, ⟨x, ?_, ?_⟩, ?_⟩
  -- `(s ∪ v) \ u ∈ ∂ 𝒜` is pretty direct:
  · exact notMem_sdiff_of_notMem_left (notMem_union.2 ⟨‹x ∉ s›, ‹x ∉ v›⟩)
  · rwa [← insert_sdiff_of_notMem _ ‹x ∉ u›, ← insert_union]
  -- For (s ∪ v) \ u ∉ ∂ 𝒜', we split up based on w ∈ u
  rintro ⟨w, hwB, hw𝒜'⟩
  have : v ⊆ insert w ((s ∪ v) \ u) :=
    (subset_sdiff.2 ⟨subset_union_right, hvu⟩).trans (subset_insert _ _)
  by_cases hwu : w ∈ u
  -- If `w ∈ u`, we find `z ∈ v`, and contradict `m` again
  · obtain ⟨z, hz, hxy⟩ := huv w hwu
    apply m z (disjoint_right.1 hsv hz)
    have : insert w ((s ∪ v) \ u) ∈ 𝒜 := mem_of_mem_compression hw𝒜' ‹_› (aux huv)
    have : (insert w ((s ∪ v) \ u) ∪ erase u w) \ erase v z ∈ 𝒜 := by
      refine sup_sdiff_mem_of_mem_compression (by rwa [hxy.eq]) ((erase_subset _ _).trans ‹_›) ?_
      rw [← sdiff_erase (mem_union_left _ <| hus hwu)]
      exact disjoint_sdiff
    convert! this using 1
    rw [insert_union_comm, insert_erase ‹w ∈ u›,
      sdiff_union_of_subset (hus.trans subset_union_left),
      sdiff_erase (mem_union_right _ ‹z ∈ v›), union_sdiff_cancel_right hsv]
  -- If `w ∉ u`, we contradict `m` again
  rw [mem_sdiff, ← Classical.not_imp, Classical.not_not] at hwB
  apply m w (hwu ∘ hwB ∘ mem_union_left _)
  have : (insert w ((s ∪ v) \ u) ∪ u) \ v ∈ 𝒜 :=
    sup_sdiff_mem_of_mem_compression ‹insert w ((s ∪ v) \ u) ∈ 𝒜'› ‹_›
      (disjoint_insert_right.2 ⟨‹_›, disjoint_sdiff⟩)
  convert! this using 1
  rw [insert_union, sdiff_union_of_subset (hus.trans subset_union_left),
    insert_sdiff_of_notMem _ (hwu ∘ hwB ∘ mem_union_right _), union_sdiff_cancel_right hsv]

/-- UV-compression reduces the size of the shadow of `𝒜` if, for all `x ∈ u` there is `y ∈ v`
such that `𝒜` is `(u.erase x, v.erase y)`-compressed. This is the key UV-compression fact needed for
Kruskal-Katona. -/
/-
**UV.card_shadow_compression_le** 是 Mathlib 中的一个定理，位于命名空间 `UV`。
形式化陈述：card_shadow_compression_le (u v : Finset α) (huv : forall x in u, exists y
 in v, IsCompressed (u.erase x) (v.erase y) 𝒜) : #(∂ (𝓒 u v 𝒜)) <= #(∂ 𝒜)
参数：u v : Finset α；huv : forall x in u, exists y in v, IsCompressed (u.erase x) (
v.erase y) 𝒜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用定理 `UV.shadow_compression_subset_compression_shadow`：shadow_compression_subs
et_compression_shadow (u v : Finset α) (huv : forall x in u, exists y in v, IsCo
mpressed (u.erase x) (v.erase y) 𝒜) :…
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `UV.card_compression`：card_compression (u v : α) (s : Finset α) : #(𝓒 u v
 s) = #s

--- 原说明 ---
UV-compression reduces the size of the shadow of `𝒜` if, for all `x ∈ u` there i
s `y ∈ v`
such that `𝒜` is `(u.erase x, v.erase y)`-compressed. This is the key UV-compres
sion fact needed for
Kruskal-Katona.
-/
theorem card_shadow_compression_le (u v : Finset α)
    (huv : ∀ x ∈ u, ∃ y ∈ v, IsCompressed (u.erase x) (v.erase y) 𝒜) :
    #(∂ (𝓒 u v 𝒜)) ≤ #(∂ 𝒜) :=
  (card_le_card <| shadow_compression_subset_compression_shadow _ _ huv).trans
    (card_compression _ _ _).le

end UV

