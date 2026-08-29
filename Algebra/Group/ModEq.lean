/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Torsion
import Mathlib.Tactic.TermCongr
import Mathlib.Tactic.Use

/-!
# Equality modulo an element

This file defines equality modulo an element in an additive commutative monoid.
In case of a group, `a` and `b` are congruent modulo `p` iff `b - a ∈ zmultiples p`.

In case of a monoid, the definition is a bit more complicated,
and it is given with the use case of natural numbers in mind.

## Main definitions

* `a ≡ b [PMOD p]`: `a` and `b` are congruent modulo `p`.

## See also

`SModEq` is a generalisation to arbitrary submodules.

## TODO

- Delete `Nat.ModEq` and `Int.ModEq` in favour of `AddCommGroup.ModEq`.
- Relate to `SModEq`.
-/

public section

assert_not_exists Module IsOrderedMonoid Function.support

namespace AddCommGroup

section AddCommMonoid
variable {M : Type*} [AddCommMonoid M] {a b c d p : M}

/--
Definition of `ModEq` / `ModEq` 的定义

English:
definition ModEq
  signature: (p a b : M)
  body: exists m n : Nat, m • p + a = n • p + b

@[inherit_doc]
notation:50 a " ≡ " b " [PMOD " p "]" => ModEq p a b

中文:
定义 ModEq
  签名: (p a b : M)
  定义体: exists m n : Nat, m • p + a = n • p + b

@[inherit_doc]
notation:50 a " ≡ " b " [PMOD " p "]" => ModEq p a b
-/
def ModEq (p a b : M) : Prop :=
  exists m n : Nat, m • p + a = n • p + b

@[inherit_doc]
notation:50 a " ≡ " b " [PMOD " p "]" => ModEq p a b

/--
theorem `modEq_iff_nsmul` / 定理 `modEq_iff_nsmul`

English:
theorem modEq_iff_nsmul
  statement: a ≡ b [PMOD p] ↔ exists m n : Nat, m • p + a = n • p + b
  proof: by
  rfl

@[refl, simp]

中文:
定理 modEq_iff_nsmul
  结论: a ≡ b [PMOD p] ↔ 存在 m n : 自然数, m • p + a = n • p + b
  证明: by
  rfl

@[refl, simp]
-/
theorem modEq_iff_nsmul : a ≡ b [PMOD p] ↔ exists m n : Nat, m • p + a = n • p + b := by
  rfl

@[refl, simp]
/--
theorem `modEq_refl` / 定理 `modEq_refl`

English:
theorem modEq_refl
  given: (a : M)
  statement: a ≡ a [PMOD p]
  proof: ⟨0, 0, by simp⟩

中文:
定理 modEq_refl
  条件: (a : M)
  结论: a ≡ a [PMOD p]
  证明: ⟨0, 0, by simp⟩
-/
theorem modEq_refl (a : M) : a ≡ a [PMOD p] :=
  ⟨0, 0, by simp⟩

/--
theorem `modEq_rfl` / 定理 `modEq_rfl`

English:
theorem modEq_rfl
  statement: a ≡ a [PMOD p]
  proof: modEq_refl _

中文:
定理 modEq_rfl
  结论: a ≡ a [PMOD p]
  证明: modEq_refl _

Depends on / 依赖: modEq_refl
-/
theorem modEq_rfl : a ≡ a [PMOD p] :=
  modEq_refl _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Std.Refl (ModEq p)
  body: ⟨modEq_refl⟩

@[symm]

中文:
实例 :
  签名: Std.Refl (ModEq p)
  定义体: ⟨modEq_refl⟩

@[symm]

Depends on / 依赖: modEq_refl
-/
instance : Std.Refl (ModEq p) := ⟨modEq_refl⟩

@[symm]
/--
theorem `ModEq.symm` / 定理 `ModEq.symm`

English:
theorem ModEq.symm
  given: (h : a ≡ b [PMOD p])
  statement: b ≡ a [PMOD p]
  proof: by
  rw [modEq_iff_nsmul] at *
  rcases h with ⟨m, n, h⟩
  exact ⟨n, m, h.symm⟩

中文:
定理 ModEq.symm
  条件: (h : a ≡ b [PMOD p])
  结论: b ≡ a [PMOD p]
  证明: by
  rw [modEq_iff_nsmul] at *
  rcases h with ⟨m, n, h⟩
  exact ⟨n, m, h.symm⟩
-/
protected theorem ModEq.symm (h : a ≡ b [PMOD p]) : b ≡ a [PMOD p] := by
  rw [modEq_iff_nsmul] at *
  rcases h with ⟨m, n, h⟩
  exact ⟨n, m, h.symm⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Std.Symm (ModEq p)
  body: ⟨fun _ _ => .symm⟩

中文:
实例 :
  签名: Std.Symm (ModEq p)
  定义体: ⟨fun _ _ => .symm⟩
-/
instance : Std.Symm (ModEq p) := ⟨fun _ _ => .symm⟩

/--
theorem `modEq_comm` / 定理 `modEq_comm`

English:
theorem modEq_comm
  statement: a ≡ b [PMOD p] ↔ b ≡ a [PMOD p]
  proof: ⟨.symm, .symm⟩

@[trans]

中文:
定理 modEq_comm
  结论: a ≡ b [PMOD p] ↔ b ≡ a [PMOD p]
  证明: ⟨.symm, .symm⟩

@[trans]
-/
theorem modEq_comm : a ≡ b [PMOD p] ↔ b ≡ a [PMOD p] := ⟨.symm, .symm⟩

@[trans]
/--
theorem `ModEq.trans` / 定理 `ModEq.trans`

English:
theorem ModEq.trans
  given: (hab : a ≡ b [PMOD p]) (hbc : b ≡ c [PMOD p])
  proof: by
  rw [modEq_iff_nsmul] at *
  rcases hab with ⟨m, n, hab⟩
  rcases hbc with ⟨k, l, hbc⟩
  use k + m, n + l
  rw [add_nsmul]; rw [add_assoc]; rw [hab]; rw [add_nsmul]; rw [add_assoc]; rw [← hbc]; rw [add_left_comm]

中文:
定理 ModEq.trans
  条件: (hab : a ≡ b [PMOD p]) (hbc : b ≡ c [PMOD p])
  证明: by
  rw [modEq_iff_nsmul] at *
  rcases hab with ⟨m, n, hab⟩
  rcases hbc with ⟨k, l, hbc⟩
  use k + m, n + l
  rw [add_nsmul]; rw [add_assoc]; rw [hab]; rw [add_nsmul]; rw [add_assoc]; rw [← hbc]; rw [add_left_comm]
-/
protected theorem ModEq.trans (hab : a ≡ b [PMOD p]) (hbc : b ≡ c [PMOD p]) :
    a ≡ c [PMOD p] := by
  rw [modEq_iff_nsmul] at *
  rcases hab with ⟨m, n, hab⟩
  rcases hbc with ⟨k, l, hbc⟩
  use k + m, n + l
  rw [add_nsmul]; rw [add_assoc]; rw [hab]; rw [add_nsmul]; rw [add_assoc]; rw [← hbc]; rw [add_left_comm]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsTrans M (ModEq p)
  body: ⟨fun _ _ _ => .trans⟩

@[simp]

中文:
实例 :
  签名: 是Trans M (ModEq p)
  定义体: ⟨fun _ _ _ => .trans⟩

@[simp]
-/
instance : IsTrans M (ModEq p) := ⟨fun _ _ _ => .trans⟩

@[simp]
/--
theorem `modEq_zero` / 定理 `modEq_zero`

English:
theorem modEq_zero
  statement: a ≡ b [PMOD 0] ↔ a = b
  proof: by simp [modEq_iff_nsmul]

@[simp]

中文:
定理 modEq_zero
  结论: a ≡ b [PMOD 0] ↔ a = b
  证明: by simp [modEq_iff_nsmul]

@[simp]

Depends on / 依赖: modEq_iff_nsmul
-/
theorem modEq_zero : a ≡ b [PMOD 0] ↔ a = b := by simp [modEq_iff_nsmul]

@[simp]
/--
theorem `self_modEq_zero` / 定理 `self_modEq_zero`

English:
theorem self_modEq_zero
  statement: p ≡ 0 [PMOD p]
  proof: modEq_iff_nsmul.mpr ⟨0, 1, by simp [one_nsmul]⟩

中文:
定理 self_modEq_zero
  结论: p ≡ 0 [PMOD p]
  证明: modEq_iff_nsmul.mpr ⟨0, 1, by simp [one_nsmul]⟩

Depends on / 依赖: modEq_iff_nsmul, modEq_iff_nsmul.mpr, one_nsmul
-/
theorem self_modEq_zero : p ≡ 0 [PMOD p] :=
  modEq_iff_nsmul.mpr ⟨0, 1, by simp [one_nsmul]⟩

/--
theorem `add_nsmul_modEq` / 定理 `add_nsmul_modEq`

English:
theorem add_nsmul_modEq
  given: (n : Nat)
  statement: a + n • p ≡ a [PMOD p]
  proof: modEq_iff_nsmul.mpr ⟨0, n, by simp [add_comm]⟩

中文:
定理 add_nsmul_modEq
  条件: (n : 自然数)
  结论: a + n • p ≡ a [PMOD p]
  证明: modEq_iff_nsmul.mpr ⟨0, n, by simp [add_comm]⟩

Depends on / 依赖: add_comm, modEq_iff_nsmul, modEq_iff_nsmul.mpr
-/
theorem add_nsmul_modEq (n : Nat) : a + n • p ≡ a [PMOD p] :=
  modEq_iff_nsmul.mpr ⟨0, n, by simp [add_comm]⟩

/--
theorem `nsmul_add_modEq` / 定理 `nsmul_add_modEq`

English:
theorem nsmul_add_modEq
  given: (n : Nat)
  statement: n • p + a ≡ a [PMOD p]
  proof: modEq_iff_nsmul.mpr ⟨0, n, by simp⟩

中文:
定理 nsmul_add_modEq
  条件: (n : 自然数)
  结论: n • p + a ≡ a [PMOD p]
  证明: modEq_iff_nsmul.mpr ⟨0, n, by simp⟩

Depends on / 依赖: modEq_iff_nsmul, modEq_iff_nsmul.mpr
-/
theorem nsmul_add_modEq (n : Nat) : n • p + a ≡ a [PMOD p] :=
  modEq_iff_nsmul.mpr ⟨0, n, by simp⟩

namespace ModEq

/--
theorem `add` / 定理 `add`

English:
theorem add
  given: (hab : a ≡ b [PMOD p]) (hcd : c ≡ d [PMOD p])
  proof: by
  rw [modEq_iff_nsmul] at *
  rcases hab with ⟨k, l, hab⟩
  rcases hcd with ⟨m, n, hcd⟩
  use k + m, l + n
  rw [add_nsmul]; rw [add_add_add_comm]; rw [hab]; rw [hcd]; rw [add_nsmul]; rw [add_add_add_comm]

中文:
定理 add
  条件: (hab : a ≡ b [PMOD p]) (hcd : c ≡ d [PMOD p])
  证明: by
  rw [modEq_iff_nsmul] at *
  rcases hab with ⟨k, l, hab⟩
  rcases hcd with ⟨m, n, hcd⟩
  use k + m, l + n
  rw [add_nsmul]; rw [add_add_add_comm]; rw [hab]; rw [hcd]; rw [add_nsmul]; rw [add_add_add_comm]
-/
protected theorem add (hab : a ≡ b [PMOD p]) (hcd : c ≡ d [PMOD p]) :
    a + c ≡ b + d [PMOD p] := by
  rw [modEq_iff_nsmul] at *
  rcases hab with ⟨k, l, hab⟩
  rcases hcd with ⟨m, n, hcd⟩
  use k + m, l + n
  rw [add_nsmul]; rw [add_add_add_comm]; rw [hab]; rw [hcd]; rw [add_nsmul]; rw [add_add_add_comm]

/--
theorem `add_left` / 定理 `add_left`

English:
theorem add_left
  given: (c : M) (h : a ≡ b [PMOD p])
  statement: c + a ≡ c + b [PMOD p]
  proof: modEq_rfl.add h

中文:
定理 add_left
  条件: (c : M) (h : a ≡ b [PMOD p])
  结论: c + a ≡ c + b [PMOD p]
  证明: modEq_rfl.add h
-/
protected theorem add_left (c : M) (h : a ≡ b [PMOD p]) : c + a ≡ c + b [PMOD p] :=
  modEq_rfl.add h

/--
theorem `add_right` / 定理 `add_right`

English:
theorem add_right
  given: (c : M) (h : a ≡ b [PMOD p])
  statement: a + c ≡ b + c [PMOD p]
  proof: h.add modEq_rfl

中文:
定理 add_right
  条件: (c : M) (h : a ≡ b [PMOD p])
  结论: a + c ≡ b + c [PMOD p]
  证明: h.add modEq_rfl
-/
protected theorem add_right (c : M) (h : a ≡ b [PMOD p]) : a + c ≡ b + c [PMOD p] :=
  h.add modEq_rfl

/--
theorem `of_nsmul` / 定理 `of_nsmul`

English:
theorem of_nsmul
  given: {n : Nat}
  statement: a ≡ b [PMOD n • p] -> a ≡ b [PMOD p]
  proof: fun ⟨k, l, h⟩ =>
  ⟨k * n, l * n, by simpa [mul_nsmul']⟩

中文:
定理 of_nsmul
  条件: {n : 自然数}
  结论: a ≡ b [PMOD n • p] -> a ≡ b [PMOD p]
  证明: fun ⟨k, l, h⟩ =>
  ⟨k * n, l * n, by simpa [mul_nsmul']⟩
-/
protected theorem of_nsmul {n : Nat} : a ≡ b [PMOD n • p] -> a ≡ b [PMOD p] := fun ⟨k, l, h⟩ =>
  ⟨k * n, l * n, by simpa [mul_nsmul']⟩

/--
theorem `nsmul` / 定理 `nsmul`

English:
theorem nsmul
  given: {n : Nat} (h : a ≡ b [PMOD p])
  statement: n • a ≡ n • b [PMOD n • p]
  proof: by
  rw [modEq_iff_nsmul] at *
  rcases h with ⟨k, l, h⟩
  use k, l
  rw [← mul_nsmul]; rw [mul_nsmul']; rw [← nsmul_add]; rw [h]; rw [nsmul_add]; rw [← mul_nsmul]; rw [mul_nsmul']

中文:
定理 nsmul
  条件: {n : 自然数} (h : a ≡ b [PMOD p])
  结论: n • a ≡ n • b [PMOD n • p]
  证明: by
  rw [modEq_iff_nsmul] at *
  rcases h with ⟨k, l, h⟩
  use k, l
  rw [← mul_nsmul]; rw [mul_nsmul']; rw [← nsmul_add]; rw [h]; rw [nsmul_add]; rw [← mul_nsmul]; rw [mul_nsmul']
-/
protected theorem nsmul {n : Nat} (h : a ≡ b [PMOD p]) : n • a ≡ n • b [PMOD n • p] := by
  rw [modEq_iff_nsmul] at *
  rcases h with ⟨k, l, h⟩
  use k, l
  rw [← mul_nsmul]; rw [mul_nsmul']; rw [← nsmul_add]; rw [h]; rw [nsmul_add]; rw [← mul_nsmul]; rw [mul_nsmul']

/--
theorem `add_nsmul` / 定理 `add_nsmul`

English:
theorem add_nsmul
  given: (n : Nat)
  statement: a ≡ b [PMOD p] -> a + n • p ≡ b [PMOD p]
  proof: (add_nsmul_modEq _).trans

中文:
定理 add_nsmul
  条件: (n : 自然数)
  结论: a ≡ b [PMOD p] -> a + n • p ≡ b [PMOD p]
  证明: (add_nsmul_modEq _).trans
-/
protected theorem add_nsmul (n : Nat) : a ≡ b [PMOD p] -> a + n • p ≡ b [PMOD p] :=
  (add_nsmul_modEq _).trans

/--
theorem `nsmul_add` / 定理 `nsmul_add`

English:
theorem nsmul_add
  given: (n : Nat)
  statement: a ≡ b [PMOD p] -> n • p + a ≡ b [PMOD p]
  proof: (nsmul_add_modEq _).trans

中文:
定理 nsmul_add
  条件: (n : 自然数)
  结论: a ≡ b [PMOD p] -> n • p + a ≡ b [PMOD p]
  证明: (nsmul_add_modEq _).trans
-/
protected theorem nsmul_add (n : Nat) : a ≡ b [PMOD p] -> n • p + a ≡ b [PMOD p] :=
  (nsmul_add_modEq _).trans

/--
theorem `map` / 定理 `map`

English:
theorem map
  statement: {N F : Type*} [AddCommMonoid N] [FunLike F M N] [AddMonoidHomClass F M N]
  proof: by
  rw [modEq_iff_nsmul] at *
  rcases h with ⟨m, n, h⟩
  use m, n
  simpa using congr(f $h)

中文:
定理 map
  结论: {N F : 类型} [加法交换幺半群 N] [函数状 F M N] [加法幺半群态射类 F M N]
  证明: by
  rw [modEq_iff_nsmul] at *
  rcases h with ⟨m, n, h⟩
  use m, n
  simpa using congr(f $h)

Depends on / 依赖: modEq_iff_nsmul
-/
theorem map {N F : Type*} [AddCommMonoid N] [FunLike F M N] [AddMonoidHomClass F M N]
    (f : F) (h : a ≡ b [PMOD p]) : f a ≡ f b [PMOD f p] := by
  rw [modEq_iff_nsmul] at *
  rcases h with ⟨m, n, h⟩
  use m, n
  simpa using congr(f $h)

end ModEq

/--
theorem `map_modEq_iff` / 定理 `map_modEq_iff`

English:
theorem map_modEq_iff
  statement: {N F : Type*} [AddCommMonoid N] [FunLike F M N] [AddMonoidHomClass F M N]
  proof: by
  simp only [modEq_iff_nsmul, ← map_nsmul, ← map_add, hf.eq_iff]

@[simp]

中文:
定理 map_modEq_iff
  结论: {N F : 类型} [加法交换幺半群 N] [函数状 F M N] [加法幺半群态射类 F M N]
  证明: by
  simp only [modEq_iff_nsmul, ← map_nsmul, ← map_add, hf.eq_iff]

@[simp]

Depends on / 依赖: eq_iff, hf.eq_iff, map_add, map_nsmul, modEq_iff_nsmul
-/
theorem map_modEq_iff {N F : Type*} [AddCommMonoid N] [FunLike F M N] [AddMonoidHomClass F M N]
    (f : F) (hf : Function.Injective f) : f a ≡ f b [PMOD f p] ↔ a ≡ b [PMOD p] := by
  simp only [modEq_iff_nsmul, ← map_nsmul, ← map_add, hf.eq_iff]

@[simp]
/--
theorem `nsmul_modEq_nsmul` / 定理 `nsmul_modEq_nsmul`

English:
theorem nsmul_modEq_nsmul
  given: [IsAddTorsionFree M] {n : Nat} (hn : n != 0)
  proof: by
  simp only [modEq_iff_nsmul, ← mul_nsmul _ n, mul_nsmul' _ n, ← nsmul_add, nsmul_right_inj hn]

alias ⟨ModEq.nsmul_cancel, _⟩ := nsmul_modEq_nsmul

中文:
定理 nsmul_modEq_nsmul
  条件: [是加法无挠 M] {n : 自然数} (hn : n != 0)
  证明: by
  simp only [modEq_iff_nsmul, ← mul_nsmul _ n, mul_nsmul' _ n, ← nsmul_add, nsmul_right_inj hn]

alias ⟨ModEq.nsmul_cancel, _⟩ := nsmul_modEq_nsmul

Depends on / 依赖: modEq_iff_nsmul, mul_nsmul, nsmul_add, nsmul_right_inj
-/
theorem nsmul_modEq_nsmul [IsAddTorsionFree M] {n : Nat} (hn : n != 0) :
    n • a ≡ n • b [PMOD n • p] ↔ a ≡ b [PMOD p] := by
  simp only [modEq_iff_nsmul, ← mul_nsmul _ n, mul_nsmul' _ n, ← nsmul_add, nsmul_right_inj hn]

alias ⟨ModEq.nsmul_cancel, _⟩ := nsmul_modEq_nsmul

end AddCommMonoid

section AddCancelCommMonoid
variable {M : Type*} [AddCancelCommMonoid M] {a b c d p : M}

namespace ModEq

@[simp]
/--
theorem `add_iff_left` / 定理 `add_iff_left`

English:
theorem add_iff_left
  given: (h : a ≡ b [PMOD p])
  proof: by
  refine ⟨fun hadd => ?_, h.add⟩
  rw [modEq_iff_nsmul] at *
  rcases h with ⟨k, l, h⟩
  rcases hadd with ⟨m, n, hadd⟩
  use m + l, n + k
  apply add_right_cancel (b := a)
  rw [add_assoc]; rw [add_comm c]; rw [add_nsmul]; rw [add_right_comm]; rw [hadd]; rw [← add_assoc]; rw [add_right_comm _ b]; rw [add_right_comm _ b]; rw [add_assoc]; rw [← h]; rw [add_add_add_comm]; rw [add_nsmul]; rw [← add_assoc]

@[simp]

中文:
定理 add_iff_left
  条件: (h : a ≡ b [PMOD p])
  证明: by
  refine ⟨fun hadd => ?_, h.add⟩
  rw [modEq_iff_nsmul] at *
  rcases h with ⟨k, l, h⟩
  rcases hadd with ⟨m, n, hadd⟩
  use m + l, n + k
  apply add_right_cancel (b := a)
  rw [add_assoc]; rw [add_comm c]; rw [add_nsmul]; rw [add_right_comm]; rw [hadd]; rw [← add_assoc]; rw [add_right_comm _ b]; rw [add_right_comm _ b]; rw [add_assoc]; rw [← h]; rw [add_add_add_comm]; rw [add_nsmul]; rw [← add_assoc]

@[simp]
-/
protected theorem add_iff_left (h : a ≡ b [PMOD p]) :
    a + c ≡ b + d [PMOD p] ↔ c ≡ d [PMOD p] := by
  refine ⟨fun hadd => ?_, h.add⟩
  rw [modEq_iff_nsmul] at *
  rcases h with ⟨k, l, h⟩
  rcases hadd with ⟨m, n, hadd⟩
  use m + l, n + k
  apply add_right_cancel (b := a)
  rw [add_assoc]; rw [add_comm c]; rw [add_nsmul]; rw [add_right_comm]; rw [hadd]; rw [← add_assoc]; rw [add_right_comm _ b]; rw [add_right_comm _ b]; rw [add_assoc]; rw [← h]; rw [add_add_add_comm]; rw [add_nsmul]; rw [← add_assoc]

@[simp]
/--
theorem `add_iff_right` / 定理 `add_iff_right`

English:
theorem add_iff_right
  given: (h : c ≡ d [PMOD p])
  proof: by
  simpa only [add_comm c, add_comm d] using h.add_iff_left

protected alias ⟨add_left_cancel, _⟩ := ModEq.add_iff_left

protected alias ⟨add_right_cancel, _⟩ := ModEq.add_iff_right

中文:
定理 add_iff_right
  条件: (h : c ≡ d [PMOD p])
  证明: by
  simpa only [add_comm c, add_comm d] using h.add_iff_left

protected alias ⟨add_left_cancel, _⟩ := ModEq.add_iff_left

protected alias ⟨add_right_cancel, _⟩ := ModEq.add_iff_right
-/
protected theorem add_iff_right (h : c ≡ d [PMOD p]) :
    a + c ≡ b + d [PMOD p] ↔ a ≡ b [PMOD p] := by
  simpa only [add_comm c, add_comm d] using h.add_iff_left

protected alias ⟨add_left_cancel, _⟩ := ModEq.add_iff_left

protected alias ⟨add_right_cancel, _⟩ := ModEq.add_iff_right

/--
theorem `add_left_cancel'` / 定理 `add_left_cancel'`

English:
theorem add_left_cancel'
  given: (c : M)
  statement: c + a ≡ c + b [PMOD p] -> a ≡ b [PMOD p]
  proof: modEq_rfl.add_left_cancel

中文:
定理 add_left_cancel'
  条件: (c : M)
  结论: c + a ≡ c + b [PMOD p] -> a ≡ b [PMOD p]
  证明: modEq_rfl.add_left_cancel
-/
protected theorem add_left_cancel' (c : M) : c + a ≡ c + b [PMOD p] -> a ≡ b [PMOD p] :=
  modEq_rfl.add_left_cancel

/--
theorem `add_right_cancel'` / 定理 `add_right_cancel'`

English:
theorem add_right_cancel'
  given: (c : M)
  statement: a + c ≡ b + c [PMOD p] -> a ≡ b [PMOD p]
  proof: modEq_rfl.add_right_cancel

中文:
定理 add_right_cancel'
  条件: (c : M)
  结论: a + c ≡ b + c [PMOD p] -> a ≡ b [PMOD p]
  证明: modEq_rfl.add_right_cancel
-/
protected theorem add_right_cancel' (c : M) : a + c ≡ b + c [PMOD p] -> a ≡ b [PMOD p] :=
  modEq_rfl.add_right_cancel

end ModEq

@[simp]
/--
theorem `add_modEq_left` / 定理 `add_modEq_left`

English:
theorem add_modEq_left
  statement: a + b ≡ a [PMOD p] ↔ b ≡ 0 [PMOD p]
  proof: by
  simpa using (modEq_refl a).add_iff_left (d := 0)

@[simp]

中文:
定理 add_modEq_left
  结论: a + b ≡ a [PMOD p] ↔ b ≡ 0 [PMOD p]
  证明: by
  simpa using (modEq_refl a).add_iff_left (d := 0)

@[simp]

Depends on / 依赖: add_iff_left, modEq_refl
-/
theorem add_modEq_left : a + b ≡ a [PMOD p] ↔ b ≡ 0 [PMOD p] := by
  simpa using (modEq_refl a).add_iff_left (d := 0)

@[simp]
/--
theorem `add_modEq_right` / 定理 `add_modEq_right`

English:
theorem add_modEq_right
  statement: a + b ≡ b [PMOD p] ↔ a ≡ 0 [PMOD p]
  proof: by simp [add_comm a]

中文:
定理 add_modEq_right
  结论: a + b ≡ b [PMOD p] ↔ a ≡ 0 [PMOD p]
  证明: by simp [add_comm a]

Depends on / 依赖: add_comm
-/
theorem add_modEq_right : a + b ≡ b [PMOD p] ↔ a ≡ 0 [PMOD p] := by simp [add_comm a]

end AddCancelCommMonoid

section AddCommGroup
variable {G : Type*} [AddCommGroup G] {p a a₁ a₂ b b₁ b₂ c : G} {n : Nat} {z : Int}

/--
theorem `modEq_iff_zsmul` / 定理 `modEq_iff_zsmul`

English:
theorem modEq_iff_zsmul
  statement: a ≡ b [PMOD p] ↔ exists m : Int, m • p = b - a
  proof: by
  rw [modEq_iff_nsmul]
  constructor
  · rintro ⟨m, n, h⟩
    use m - n
    rw [sub_zsmul]; rw [← sub_eq_add_neg]; rw [sub_eq_sub_iff_add_eq_add]; rw [add_comm b]
    exact mod_cast h
  · rintro ⟨m, h⟩
    use m.toNat, (-m).toNat
    rwa [add_comm _ b, ← sub_eq_sub_iff_add_eq_add, ← natCast_zsmul, ← natCast_zsmul,
      sub_eq_add_neg, ← sub_zsmul, m.toNat_sub_toNat_neg]

中文:
定理 modEq_iff_zsmul
  结论: a ≡ b [PMOD p] ↔ 存在 m : 整数, m • p = b - a
  证明: by
  rw [modEq_iff_nsmul]
  constructor
  · rintro ⟨m, n, h⟩
    use m - n
    rw [sub_zsmul]; rw [← sub_eq_add_neg]; rw [sub_eq_sub_iff_add_eq_add]; rw [add_comm b]
    exact mod_cast h
  · rintro ⟨m, h⟩
    use m.toNat, (-m).toNat
    rwa [add_comm _ b, ← sub_eq_sub_iff_add_eq_add, ← natCast_zsmul, ← natCast_zsmul,
      sub_eq_add_neg, ← sub_zsmul, m.toNat_sub_toNat_neg]

Depends on / 依赖: add_comm, m.toNat, m.toNat_sub_toNat_neg, modEq_iff_nsmul, mod_cast, natCast_zsmul, sub_eq_add_neg, sub_eq_sub_iff_add_eq_add, sub_zsmul, toNat_sub_toNat_neg
-/
theorem modEq_iff_zsmul : a ≡ b [PMOD p] ↔ exists m : Int, m • p = b - a := by
  rw [modEq_iff_nsmul]
  constructor
  · rintro ⟨m, n, h⟩
    use m - n
    rw [sub_zsmul]; rw [← sub_eq_add_neg]; rw [sub_eq_sub_iff_add_eq_add]; rw [add_comm b]
    exact mod_cast h
  · rintro ⟨m, h⟩
    use m.toNat, (-m).toNat
    rwa [add_comm _ b, ← sub_eq_sub_iff_add_eq_add, ← natCast_zsmul, ← natCast_zsmul,
      sub_eq_add_neg, ← sub_zsmul, m.toNat_sub_toNat_neg]

/--
theorem `modEq_iff_zsmul'` / 定理 `modEq_iff_zsmul'`

English:
theorem modEq_iff_zsmul'
  statement: a ≡ b [PMOD p] ↔ exists m : Int, b - a = m • p
  proof: by
  simp only [modEq_iff_zsmul, eq_comm]

@[simp]

中文:
定理 modEq_iff_zsmul'
  结论: a ≡ b [PMOD p] ↔ 存在 m : 整数, b - a = m • p
  证明: by
  simp only [modEq_iff_zsmul, eq_comm]

@[simp]

Depends on / 依赖: eq_comm, modEq_iff_zsmul
-/
theorem modEq_iff_zsmul' : a ≡ b [PMOD p] ↔ exists m : Int, b - a = m • p := by
  simp only [modEq_iff_zsmul, eq_comm]

@[simp]
/--
theorem `neg_modEq_neg` / 定理 `neg_modEq_neg`

English:
theorem neg_modEq_neg
  statement: -a ≡ -b [PMOD p] ↔ a ≡ b [PMOD p]
  proof: modEq_comm.trans by simp [modEq_iff_zsmul, neg_add_eq_sub]

alias ⟨ModEq.of_neg, ModEq.neg⟩ := neg_modEq_neg

@[simp]

中文:
定理 neg_modEq_neg
  结论: -a ≡ -b [PMOD p] ↔ a ≡ b [PMOD p]
  证明: modEq_comm.trans by simp [modEq_iff_zsmul, neg_add_eq_sub]

alias ⟨ModEq.of_neg, ModEq.neg⟩ := neg_modEq_neg

@[simp]

Depends on / 依赖: modEq_comm, modEq_comm.trans, modEq_iff_zsmul, neg_add_eq_sub
-/
theorem neg_modEq_neg : -a ≡ -b [PMOD p] ↔ a ≡ b [PMOD p] :=
modEq_comm.trans by simp [modEq_iff_zsmul, neg_add_eq_sub]

alias ⟨ModEq.of_neg, ModEq.neg⟩ := neg_modEq_neg

@[simp]
/--
theorem `modEq_neg` / 定理 `modEq_neg`

English:
theorem modEq_neg
  statement: a ≡ b [PMOD -p] ↔ a ≡ b [PMOD p]
  proof: modEq_comm.trans by simp [modEq_iff_zsmul, neg_eq_iff_eq_neg]

alias ⟨ModEq.of_neg', ModEq.neg'⟩ := modEq_neg

中文:
定理 modEq_neg
  结论: a ≡ b [PMOD -p] ↔ a ≡ b [PMOD p]
  证明: modEq_comm.trans by simp [modEq_iff_zsmul, neg_eq_iff_eq_neg]

alias ⟨ModEq.of_neg', ModEq.neg'⟩ := modEq_neg

Depends on / 依赖: modEq_comm, modEq_comm.trans, modEq_iff_zsmul, neg_eq_iff_eq_neg
-/
theorem modEq_neg : a ≡ b [PMOD -p] ↔ a ≡ b [PMOD p] :=
modEq_comm.trans by simp [modEq_iff_zsmul, neg_eq_iff_eq_neg]

alias ⟨ModEq.of_neg', ModEq.neg'⟩ := modEq_neg

/--
theorem `modEq_sub` / 定理 `modEq_sub`

English:
theorem modEq_sub
  given: (a b : G)
  statement: a ≡ b [PMOD b - a]
  proof: ⟨1, 0, by simp [one_nsmul]⟩

@[simp]

中文:
定理 modEq_sub
  条件: (a b : G)
  结论: a ≡ b [PMOD b - a]
  证明: ⟨1, 0, by simp [one_nsmul]⟩

@[simp]

Depends on / 依赖: one_nsmul
-/
theorem modEq_sub (a b : G) : a ≡ b [PMOD b - a] :=
  ⟨1, 0, by simp [one_nsmul]⟩

@[simp]
/--
theorem `zsmul_modEq_zero` / 定理 `zsmul_modEq_zero`

English:
theorem zsmul_modEq_zero
  given: (z : Int)
  statement: z • p ≡ 0 [PMOD p]
  proof: modEq_iff_zsmul.mpr ⟨-z, by simp⟩

中文:
定理 zsmul_modEq_zero
  条件: (z : 整数)
  结论: z • p ≡ 0 [PMOD p]
  证明: modEq_iff_zsmul.mpr ⟨-z, by simp⟩

Depends on / 依赖: modEq_iff_zsmul, modEq_iff_zsmul.mpr
-/
theorem zsmul_modEq_zero (z : Int) : z • p ≡ 0 [PMOD p] :=
  modEq_iff_zsmul.mpr ⟨-z, by simp⟩

/--
theorem `add_zsmul_modEq` / 定理 `add_zsmul_modEq`

English:
theorem add_zsmul_modEq
  given: (z : Int)
  statement: a + z • p ≡ a [PMOD p]
  proof: modEq_iff_zsmul.mpr ⟨-z, by simp⟩

中文:
定理 add_zsmul_modEq
  条件: (z : 整数)
  结论: a + z • p ≡ a [PMOD p]
  证明: modEq_iff_zsmul.mpr ⟨-z, by simp⟩

Depends on / 依赖: modEq_iff_zsmul, modEq_iff_zsmul.mpr
-/
theorem add_zsmul_modEq (z : Int) : a + z • p ≡ a [PMOD p] :=
  modEq_iff_zsmul.mpr ⟨-z, by simp⟩

/--
theorem `zsmul_add_modEq` / 定理 `zsmul_add_modEq`

English:
theorem zsmul_add_modEq
  given: (z : Int)
  statement: z • p + a ≡ a [PMOD p]
  proof: modEq_iff_zsmul.mpr ⟨-z, by simp⟩

中文:
定理 zsmul_add_modEq
  条件: (z : 整数)
  结论: z • p + a ≡ a [PMOD p]
  证明: modEq_iff_zsmul.mpr ⟨-z, by simp⟩

Depends on / 依赖: modEq_iff_zsmul, modEq_iff_zsmul.mpr
-/
theorem zsmul_add_modEq (z : Int) : z • p + a ≡ a [PMOD p] :=
  modEq_iff_zsmul.mpr ⟨-z, by simp⟩

namespace ModEq

/--
theorem `add_zsmul` / 定理 `add_zsmul`

English:
theorem add_zsmul
  given: (z : Int)
  statement: a ≡ b [PMOD p] -> a + z • p ≡ b [PMOD p]
  proof: (add_zsmul_modEq _).trans

中文:
定理 add_zsmul
  条件: (z : 整数)
  结论: a ≡ b [PMOD p] -> a + z • p ≡ b [PMOD p]
  证明: (add_zsmul_modEq _).trans
-/
protected theorem add_zsmul (z : Int) : a ≡ b [PMOD p] -> a + z • p ≡ b [PMOD p] :=
  (add_zsmul_modEq _).trans

/--
theorem `zsmul_add` / 定理 `zsmul_add`

English:
theorem zsmul_add
  given: (z : Int)
  statement: a ≡ b [PMOD p] -> z • p + a ≡ b [PMOD p]
  proof: (zsmul_add_modEq _).trans

中文:
定理 zsmul_add
  条件: (z : 整数)
  结论: a ≡ b [PMOD p] -> z • p + a ≡ b [PMOD p]
  证明: (zsmul_add_modEq _).trans
-/
protected theorem zsmul_add (z : Int) : a ≡ b [PMOD p] -> z • p + a ≡ b [PMOD p] :=
  (zsmul_add_modEq _).trans

/--
theorem `of_zsmul` / 定理 `of_zsmul`

English:
theorem of_zsmul
  given: (h : a ≡ b [PMOD z • p])
  statement: a ≡ b [PMOD p]
  proof: by
  rw [modEq_iff_zsmul] at *
  rcases h with ⟨m, h⟩
  simp [← h, ← mul_zsmul]

中文:
定理 of_zsmul
  条件: (h : a ≡ b [PMOD z • p])
  结论: a ≡ b [PMOD p]
  证明: by
  rw [modEq_iff_zsmul] at *
  rcases h with ⟨m, h⟩
  simp [← h, ← mul_zsmul]
-/
protected theorem of_zsmul (h : a ≡ b [PMOD z • p]) : a ≡ b [PMOD p] := by
  rw [modEq_iff_zsmul] at *
  rcases h with ⟨m, h⟩
  simp [← h, ← mul_zsmul]

/--
theorem `zsmul` / 定理 `zsmul`

English:
theorem zsmul
  given: (h : a ≡ b [PMOD p])
  statement: z • a ≡ z • b [PMOD z • p]
  proof: by
  rw [modEq_iff_zsmul] at *
  rcases h with ⟨m, h⟩
  use m
  rw [← zsmul_sub]; rw [← h]; rw [← mul_zsmul]; rw [← mul_zsmul']

中文:
定理 zsmul
  条件: (h : a ≡ b [PMOD p])
  结论: z • a ≡ z • b [PMOD z • p]
  证明: by
  rw [modEq_iff_zsmul] at *
  rcases h with ⟨m, h⟩
  use m
  rw [← zsmul_sub]; rw [← h]; rw [← mul_zsmul]; rw [← mul_zsmul']
-/
protected theorem zsmul (h : a ≡ b [PMOD p]) : z • a ≡ z • b [PMOD z • p] := by
  rw [modEq_iff_zsmul] at *
  rcases h with ⟨m, h⟩
  use m
  rw [← zsmul_sub]; rw [← h]; rw [← mul_zsmul]; rw [← mul_zsmul']

end ModEq

@[simp]
/--
theorem `zsmul_modEq_zsmul` / 定理 `zsmul_modEq_zsmul`

English:
theorem zsmul_modEq_zsmul
  given: [IsAddTorsionFree G] (hn : z != 0)
  proof: by
  simp [modEq_iff_zsmul, ← zsmul_sub, zsmul_comm, zsmul_right_inj hn]

alias ⟨ModEq.zsmul_cancel, _⟩ := zsmul_modEq_zsmul

中文:
定理 zsmul_modEq_zsmul
  条件: [是加法无挠 G] (hn : z != 0)
  证明: by
  simp [modEq_iff_zsmul, ← zsmul_sub, zsmul_comm, zsmul_right_inj hn]

alias ⟨ModEq.zsmul_cancel, _⟩ := zsmul_modEq_zsmul

Depends on / 依赖: modEq_iff_zsmul, zsmul_comm, zsmul_right_inj, zsmul_sub
-/
theorem zsmul_modEq_zsmul [IsAddTorsionFree G] (hn : z != 0) :
    z • a ≡ z • b [PMOD z • p] ↔ a ≡ b [PMOD p] := by
  simp [modEq_iff_zsmul, ← zsmul_sub, zsmul_comm, zsmul_right_inj hn]

alias ⟨ModEq.zsmul_cancel, _⟩ := zsmul_modEq_zsmul

namespace ModEq

@[simp]
/--
theorem `sub_iff_left` / 定理 `sub_iff_left`

English:
theorem sub_iff_left
  given: (h : a₁ ≡ b₁ [PMOD p])
  proof: by
  simp [sub_eq_add_neg, h]

@[simp]

中文:
定理 sub_iff_left
  条件: (h : a₁ ≡ b₁ [PMOD p])
  证明: by
  simp [sub_eq_add_neg, h]

@[simp]
-/
protected theorem sub_iff_left (h : a₁ ≡ b₁ [PMOD p]) :
    a₁ - a₂ ≡ b₁ - b₂ [PMOD p] ↔ a₂ ≡ b₂ [PMOD p] := by
  simp [sub_eq_add_neg, h]

@[simp]
/--
theorem `sub_iff_right` / 定理 `sub_iff_right`

English:
theorem sub_iff_right
  given: (h : a₂ ≡ b₂ [PMOD p])
  proof: by
  simp [h, sub_eq_add_neg]

protected alias ⟨sub_left_cancel, sub⟩ := ModEq.sub_iff_left

protected alias ⟨sub_right_cancel, _⟩ := ModEq.sub_iff_right

中文:
定理 sub_iff_right
  条件: (h : a₂ ≡ b₂ [PMOD p])
  证明: by
  simp [h, sub_eq_add_neg]

protected alias ⟨sub_left_cancel, sub⟩ := ModEq.sub_iff_left

protected alias ⟨sub_right_cancel, _⟩ := ModEq.sub_iff_right
-/
protected theorem sub_iff_right (h : a₂ ≡ b₂ [PMOD p]) :
    a₁ - a₂ ≡ b₁ - b₂ [PMOD p] ↔ a₁ ≡ b₁ [PMOD p] := by
  simp [h, sub_eq_add_neg]

protected alias ⟨sub_left_cancel, sub⟩ := ModEq.sub_iff_left

protected alias ⟨sub_right_cancel, _⟩ := ModEq.sub_iff_right

/--
theorem `sub_left` / 定理 `sub_left`

English:
theorem sub_left
  given: (c : G) (h : a ≡ b [PMOD p])
  statement: c - a ≡ c - b [PMOD p]
  proof: modEq_rfl.sub h

中文:
定理 sub_left
  条件: (c : G) (h : a ≡ b [PMOD p])
  结论: c - a ≡ c - b [PMOD p]
  证明: modEq_rfl.sub h
-/
protected theorem sub_left (c : G) (h : a ≡ b [PMOD p]) : c - a ≡ c - b [PMOD p] :=
  modEq_rfl.sub h

/--
theorem `sub_right` / 定理 `sub_right`

English:
theorem sub_right
  given: (c : G) (h : a ≡ b [PMOD p])
  statement: a - c ≡ b - c [PMOD p]
  proof: h.sub modEq_rfl

中文:
定理 sub_right
  条件: (c : G) (h : a ≡ b [PMOD p])
  结论: a - c ≡ b - c [PMOD p]
  证明: h.sub modEq_rfl
-/
protected theorem sub_right (c : G) (h : a ≡ b [PMOD p]) : a - c ≡ b - c [PMOD p] :=
  h.sub modEq_rfl

/--
theorem `sub_left_cancel'` / 定理 `sub_left_cancel'`

English:
theorem sub_left_cancel'
  given: (c : G)
  statement: c - a ≡ c - b [PMOD p] -> a ≡ b [PMOD p]
  proof: modEq_rfl.sub_left_cancel

中文:
定理 sub_left_cancel'
  条件: (c : G)
  结论: c - a ≡ c - b [PMOD p] -> a ≡ b [PMOD p]
  证明: modEq_rfl.sub_left_cancel
-/
protected theorem sub_left_cancel' (c : G) : c - a ≡ c - b [PMOD p] -> a ≡ b [PMOD p] :=
  modEq_rfl.sub_left_cancel

/--
theorem `sub_right_cancel'` / 定理 `sub_right_cancel'`

English:
theorem sub_right_cancel'
  given: (c : G)
  statement: a - c ≡ b - c [PMOD p] -> a ≡ b [PMOD p]
  proof: modEq_rfl.sub_right_cancel

中文:
定理 sub_right_cancel'
  条件: (c : G)
  结论: a - c ≡ b - c [PMOD p] -> a ≡ b [PMOD p]
  证明: modEq_rfl.sub_right_cancel
-/
protected theorem sub_right_cancel' (c : G) : a - c ≡ b - c [PMOD p] -> a ≡ b [PMOD p] :=
  modEq_rfl.sub_right_cancel

end ModEq

/--
theorem `modEq_sub_iff_add_modEq'` / 定理 `modEq_sub_iff_add_modEq'`

English:
theorem modEq_sub_iff_add_modEq'
  statement: a ≡ b - c [PMOD p] ↔ c + a ≡ b [PMOD p]
  proof: by
  simp [modEq_iff_zsmul', sub_sub]

中文:
定理 modEq_sub_iff_add_modEq'
  结论: a ≡ b - c [PMOD p] ↔ c + a ≡ b [PMOD p]
  证明: by
  simp [modEq_iff_zsmul', sub_sub]

Depends on / 依赖: modEq_iff_zsmul, sub_sub
-/
theorem modEq_sub_iff_add_modEq' : a ≡ b - c [PMOD p] ↔ c + a ≡ b [PMOD p] := by
  simp [modEq_iff_zsmul', sub_sub]

/--
theorem `modEq_sub_iff_add_modEq` / 定理 `modEq_sub_iff_add_modEq`

English:
theorem modEq_sub_iff_add_modEq
  statement: a ≡ b - c [PMOD p] ↔ a + c ≡ b [PMOD p]
  proof: modEq_sub_iff_add_modEq'.trans by rw [add_comm]

中文:
定理 modEq_sub_iff_add_modEq
  结论: a ≡ b - c [PMOD p] ↔ a + c ≡ b [PMOD p]
  证明: modEq_sub_iff_add_modEq'.trans by rw [add_comm]

Depends on / 依赖: add_comm, modEq_sub_iff_add_modEq
-/
theorem modEq_sub_iff_add_modEq : a ≡ b - c [PMOD p] ↔ a + c ≡ b [PMOD p] :=
modEq_sub_iff_add_modEq'.trans by rw [add_comm]

/--
theorem `sub_modEq_iff_modEq_add'` / 定理 `sub_modEq_iff_modEq_add'`

English:
theorem sub_modEq_iff_modEq_add'
  statement: a - b ≡ c [PMOD p] ↔ a ≡ b + c [PMOD p]
  proof: modEq_comm.trans modEq_sub_iff_add_modEq'.trans modEq_comm

中文:
定理 sub_modEq_iff_modEq_add'
  结论: a - b ≡ c [PMOD p] ↔ a ≡ b + c [PMOD p]
  证明: modEq_comm.trans modEq_sub_iff_add_modEq'.trans modEq_comm

Depends on / 依赖: modEq_comm, modEq_comm.trans, modEq_sub_iff_add_modEq
-/
theorem sub_modEq_iff_modEq_add' : a - b ≡ c [PMOD p] ↔ a ≡ b + c [PMOD p] :=
modEq_comm.trans modEq_sub_iff_add_modEq'.trans modEq_comm

/--
theorem `sub_modEq_iff_modEq_add` / 定理 `sub_modEq_iff_modEq_add`

English:
theorem sub_modEq_iff_modEq_add
  statement: a - b ≡ c [PMOD p] ↔ a ≡ c + b [PMOD p]
  proof: modEq_comm.trans modEq_sub_iff_add_modEq.trans modEq_comm

@[simp]

中文:
定理 sub_modEq_iff_modEq_add
  结论: a - b ≡ c [PMOD p] ↔ a ≡ c + b [PMOD p]
  证明: modEq_comm.trans modEq_sub_iff_add_modEq.trans modEq_comm

@[simp]

Depends on / 依赖: modEq_comm, modEq_comm.trans, modEq_sub_iff_add_modEq, modEq_sub_iff_add_modEq.trans
-/
theorem sub_modEq_iff_modEq_add : a - b ≡ c [PMOD p] ↔ a ≡ c + b [PMOD p] :=
modEq_comm.trans modEq_sub_iff_add_modEq.trans modEq_comm

@[simp]
/--
theorem `sub_modEq_zero` / 定理 `sub_modEq_zero`

English:
theorem sub_modEq_zero
  statement: a - b ≡ 0 [PMOD p] ↔ a ≡ b [PMOD p]
  proof: by simp [sub_modEq_iff_modEq_add]

中文:
定理 sub_modEq_zero
  结论: a - b ≡ 0 [PMOD p] ↔ a ≡ b [PMOD p]
  证明: by simp [sub_modEq_iff_modEq_add]

Depends on / 依赖: sub_modEq_iff_modEq_add
-/
theorem sub_modEq_zero : a - b ≡ 0 [PMOD p] ↔ a ≡ b [PMOD p] := by simp [sub_modEq_iff_modEq_add]

-- this matches `Int.modEq_iff_add_fac`
/--
theorem `modEq_iff_eq_add_zsmul` / 定理 `modEq_iff_eq_add_zsmul`

English:
theorem modEq_iff_eq_add_zsmul
  statement: a ≡ b [PMOD p] ↔ exists z : Int, b = a + z • p
  proof: by
  simp_rw [modEq_iff_zsmul', sub_eq_iff_eq_add']

中文:
定理 modEq_iff_eq_add_zsmul
  结论: a ≡ b [PMOD p] ↔ 存在 z : 整数, b = a + z • p
  证明: by
  simp_rw [modEq_iff_zsmul', sub_eq_iff_eq_add']

Depends on / 依赖: modEq_iff_zsmul, simp_rw, sub_eq_iff_eq_add
-/
theorem modEq_iff_eq_add_zsmul : a ≡ b [PMOD p] ↔ exists z : Int, b = a + z • p := by
  simp_rw [modEq_iff_zsmul', sub_eq_iff_eq_add']

-- this roughly matches `Int.modEq_zero_iff_dvd`
/--
theorem `modEq_zero_iff_eq_zsmul` / 定理 `modEq_zero_iff_eq_zsmul`

English:
theorem modEq_zero_iff_eq_zsmul
  statement: a ≡ 0 [PMOD p] ↔ exists z : Int, a = z • p
  proof: by
  rw [modEq_comm]; rw [modEq_iff_eq_add_zsmul]
  simp_rw [zero_add]

中文:
定理 modEq_zero_iff_eq_zsmul
  结论: a ≡ 0 [PMOD p] ↔ 存在 z : 整数, a = z • p
  证明: by
  rw [modEq_comm]; rw [modEq_iff_eq_add_zsmul]
  simp_rw [zero_add]

Depends on / 依赖: modEq_comm, modEq_iff_eq_add_zsmul, simp_rw, zero_add
-/
theorem modEq_zero_iff_eq_zsmul : a ≡ 0 [PMOD p] ↔ exists z : Int, a = z • p := by
  rw [modEq_comm]; rw [modEq_iff_eq_add_zsmul]
  simp_rw [zero_add]

/--
theorem `not_modEq_iff_ne_add_zsmul` / 定理 `not_modEq_iff_ne_add_zsmul`

English:
theorem not_modEq_iff_ne_add_zsmul
  statement: ¬a ≡ b [PMOD p] ↔ forall z : Int, b != a + z • p
  proof: by
  rw [modEq_iff_eq_add_zsmul]; rw [not_exists]

中文:
定理 not_modEq_iff_ne_add_zsmul
  结论: ¬a ≡ b [PMOD p] ↔ 对任意 z : 整数, b != a + z • p
  证明: by
  rw [modEq_iff_eq_add_zsmul]; rw [not_exists]

Depends on / 依赖: modEq_iff_eq_add_zsmul, not_exists
-/
theorem not_modEq_iff_ne_add_zsmul : ¬a ≡ b [PMOD p] ↔ forall z : Int, b != a + z • p := by
  rw [modEq_iff_eq_add_zsmul]; rw [not_exists]

/--
theorem `modEq_nsmul_cases` / 定理 `modEq_nsmul_cases`

English:
theorem modEq_nsmul_cases
  given: (n : Nat) (hn : n != 0)
  proof: by
  simp_rw [← sub_modEq_iff_modEq_add, modEq_comm (b := b)]
  simp_rw [modEq_iff_zsmul', sub_right_comm, sub_eq_iff_eq_add (b := _ • _), ← natCast_zsmul,
    ← mul_zsmul, ← add_zsmul]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨(k % n).toNat, ?_⟩
    rw [← Int.ofNat_lt]; rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (mod_cast hn))]
    refine ⟨?_, k / n, ?_⟩
    · refine Int.emod_lt_of_pos _ ?_
      lia
    · rw [hk, Int.ediv_mul_add_emod]
  · rintro ⟨k, _, j, hj⟩
    rw [hj]
    exact ⟨_, rfl⟩

alias ⟨ModEq.nsmul_cases, _⟩ := AddCommGroup.modEq_nsmul_cases

中文:
定理 modEq_nsmul_cases
  条件: (n : 自然数) (hn : n != 0)
  证明: by
  simp_rw [← sub_modEq_iff_modEq_add, modEq_comm (b := b)]
  simp_rw [modEq_iff_zsmul', sub_right_comm, sub_eq_iff_eq_add (b := _ • _), ← natCast_zsmul,
    ← mul_zsmul, ← add_zsmul]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨(k % n).toNat, ?_⟩
    rw [← Int.ofNat_lt]; rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (mod_cast hn))]
    refine ⟨?_, k / n, ?_⟩
    · refine Int.emod_lt_of_pos _ ?_
      lia
    · rw [hk, Int.ediv_mul_add_emod]
  · rintro ⟨k, _, j, hj⟩
    rw [hj]
    exact ⟨_, rfl⟩

alias ⟨ModEq.nsmul_cases, _⟩ := AddCommGroup.modEq_nsmul_cases

Depends on / 依赖: Int.ediv_mul_add_emod, Int.emod_lt_of_pos, Int.emod_nonneg, Int.ofNat_lt, Int.toNat_of_nonneg, add_zsmul, ediv_mul_add_emod, emod_lt_of_pos, emod_nonneg, modEq_comm, modEq_iff_zsmul, mod_cast, mul_zsmul, natCast_zsmul, ofNat_lt, simp_rw, sub_eq_iff_eq_add, sub_modEq_iff_modEq_add, sub_right_comm, toNat_of_nonneg
-/
theorem modEq_nsmul_cases (n : Nat) (hn : n != 0) :
    a ≡ b [PMOD p] ↔ exists i < n, a ≡ b + i • p [PMOD (n • p)] := by
  simp_rw [← sub_modEq_iff_modEq_add, modEq_comm (b := b)]
  simp_rw [modEq_iff_zsmul', sub_right_comm, sub_eq_iff_eq_add (b := _ • _), ← natCast_zsmul,
    ← mul_zsmul, ← add_zsmul]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨(k % n).toNat, ?_⟩
    rw [← Int.ofNat_lt]; rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (mod_cast hn))]
    refine ⟨?_, k / n, ?_⟩
    · refine Int.emod_lt_of_pos _ ?_
      lia
    · rw [hk, Int.ediv_mul_add_emod]
  · rintro ⟨k, _, j, hj⟩
    rw [hj]
    exact ⟨_, rfl⟩

alias ⟨ModEq.nsmul_cases, _⟩ := AddCommGroup.modEq_nsmul_cases

end AddCommGroup

end AddCommGroup
