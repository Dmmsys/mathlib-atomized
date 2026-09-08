/-
Copyright (c) 2020 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
module

public import Mathlib.Data.List.Defs

/-!
# Lemmas about `List.*Idx` functions.

Some specification lemmas for `List.mapIdx`, `List.mapIdxM`, `List.foldlIdx` and `List.foldrIdx`.

As of 2025-01-29, these are not used anywhere in Mathlib. Moreover, with
`List.enum` and `List.enumFrom` being replaced by `List.zipIdx`
in Lean's `nightly-2025-01-29` release, they now use deprecated functions and theorems.
Rather than updating this unused material, we are deprecating it.
Anyone wanting to restore this material is welcome to do so, but will need to update uses of
`List.enum` and `List.enumFrom` to use `List.zipIdx` instead.
However, note that this material will later be implemented in the Lean standard library.
-/

public section

assert_not_exists MonoidWithZero

universe u v

open Function

namespace List

variable {α : Type u} {β : Type v}

section MapIdx

/-
**List.mapIdx_append_one** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mapIdx_append_one : forall {f : Nat -> α -> β} {l : List α} {e : α}, mapId
x f (l ++ [e]) = mapIdx f l ++ [f l.length e]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.mapIdx_concat`：∀ {α : Type u_1} {α_1 : Type u_2} {f : ℕ → α → α_1} 
{l : List α} {e : α},   List.mapIdx f (l ++ [e]) = List.mapIdx f l ++ [f l.lengt
h e]
-/
theorem mapIdx_append_one : ∀ {f : ℕ → α → β} {l : List α} {e : α},
    mapIdx f (l ++ [e]) = mapIdx f l ++ [f l.length e] :=
  mapIdx_concat
/-
**List.mapIdx_eq_ofFn** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mapIdx_eq_ofFn (l : List α) (f : Nat -> α -> β) : l.mapIdx f = ofFn fun i 
: Fin l.length => f (i : Nat) (l.get i)
参数：l : List α；f : Nat -> α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.ofFn_zero`：∀ {α : Type u_1} {f : Fin 0 → α}, List.ofFn f = []
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.lt_of_succ_lt_succ`：∀ {n m : ℕ}, n.succ < m.succ → n < m
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.mapIdx_cons`：∀ {α : Type u_1} {α_1 : Type u_2} {f : ℕ → α → α_1} {l
 : List α} {a : α},   List.mapIdx f (a :: l) = f 0 a :: List.mapIdx (fun i => f 
(i + 1…
· 使用定理 `List.ofFn_succ`：∀ {α : Type u_1} {n : ℕ} {f : Fin (n + 1) → α}, List.ofF
n f = f 0 :: List.ofFn fun i => f i.succ
-/
theorem mapIdx_eq_ofFn (l : List α) (f : ℕ → α → β) :
    l.mapIdx f = ofFn fun i : Fin l.length ↦ f (i : ℕ) (l.get i) := by
  induction l generalizing f with
  | nil => simp
  | cons _ _ IH => simp [IH]

end MapIdx

section MapIdxM'

variable {m : Type u → Type v} [Monad m] [LawfulMonad m]

/-
**List.mapIdxMAux'_eq_mapIdxMGo** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {m : Type u → Type v} [inst : Monad m] [LawfulMonad m] {α : Type u_1} (f
 : ℕ → α → m PUnit.{u + 1}) (as : List α)   (arr : Array PUnit.{u + 1}), List.ma
pIdxMAux' f arr.size as = List.mapIdxM.go f as arr *> pure PUnit.unit
参数：f : ℕ → α → m PUnit.{u + 1}；as : List α；arr : Array PUnit.{u + 1}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.mapIdxMAux'`：mapIdxMAux'_eq_mapIdxMGo {α} (f : Nat -> α -> m PUnit)
 (as : List α) (arr : Array PUnit) : mapIdxMAux' f arr.size as = mapIdxM.go f as
 arr *…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LawfulApplicative.seqRight_eq`：∀ {f : Type u → Type v} {inst : Applicati
ve f} [self : LawfulApplicative f] {α β : Type u} (x : f α) (y : f β),   x *> y 
= Function.const α …
· 使用定理 `LawfulMonad.toLawfulApplicative`：∀ {m : Type u → Type v} {inst : Monad m
} [self : LawfulMonad m], LawfulApplicative m
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LawfulApplicative.map_pure`：∀ {f : Type u → Type v} {inst : Applicative 
f} [self : LawfulApplicative f] {α β : Type u} (g : α → β) (x : α),   g <$> pure
 x = pure (g x)
· 使用定理 `LawfulApplicative.seq_pure`：∀ {f : Type u → Type v} {inst : Applicative 
f} [self : LawfulApplicative f] {α β : Type u} (g : f (α → β)) (x : α),   g <*> 
pure x = (fun h …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_eq_pure_bind`：∀ {m : Type u_1 → Type u_2} {α β : Type u_1} [inst : M
onad m] [LawfulMonad m] (f : α → β) (x : m α),   f <$> x = do     let a ← x     
pure (…
· 使用定理 `seq_eq_bind_map`：∀ {m : Type u → Type u_1} {α β : Type u} [inst : Monad 
m] [LawfulMonad m] (f : m (α → β)) (x : m α),   f <*> x = do     let x_1 ← f    
 x_1 …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `bind_pure_unit`：∀ {m : Type u_1 → Type u_2} [inst : Monad m] [LawfulMona
d m] {x : m PUnit.{u_1 + 1}},   (do       x       pure PUnit.unit) =     x
· 使用定理 `LawfulMonad.bind_assoc`：∀ {m : Type u → Type v} {inst : Monad m} [self :
 LawfulMonad m] {α β γ : Type u} (x : m α) (f : α → m β) (g : β → m γ),   x >>= 
f >>= g = x …
· 使用定理 `LawfulMonad.pure_bind`：∀ {m : Type u → Type v} {inst : Monad m} [self : 
LawfulMonad m] {α β : Type u} (x : α) (f : α → m β), pure x >>= f = f x
· 使用定理 `Array.size_push`：∀ {α : Type u} {xs : Array α} (v : α), (xs.push v).size
 = xs.size + 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mapIdxMAux'_eq_mapIdxMGo {α} (f : ℕ → α → m PUnit) (as : List α) (arr : Array PUnit) :
    mapIdxMAux' f arr.size as = mapIdxM.go f as arr *> pure PUnit.unit := by
  induction as generalizing arr with
  | nil => simp only [mapIdxMAux', mapIdxM.go, seqRight_eq, map_pure, seq_pure]
  | cons head tail ih =>
    simp only [mapIdxMAux', seqRight_eq, map_eq_pure_bind, seq_eq_bind_map, bind_pure_unit,
      LawfulMonad.bind_assoc, pure_bind, mapIdxM.go]
    generalize (f (Array.size arr) head) = head
    have : (arr.push ⟨⟩).size = arr.size + 1 := Array.size_push _
    rw [← this, ih]
    simp only [seqRight_eq, map_eq_pure_bind, seq_pure, LawfulMonad.bind_assoc, pure_bind]
/-
**List.mapIdxM'_eq_mapIdxM** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {m : Type u → Type v} [inst : Monad m] [LawfulMonad m] {α : Type u_1} (f
 : ℕ → α → m PUnit.{u + 1}) (as : List α),   List.mapIdxM' f as = List.mapIdxM f
 as *> pure PUnit.unit
参数：f : ℕ → α → m PUnit.{u + 1}；as : List α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.mapIdxMAux'_eq_mapIdxMGo`：∀ {m : Type u → Type v} [inst : Monad m] 
[LawfulMonad m] {α : Type u_1} (f : ℕ → α → m PUnit.{u + 1}) (as : List α)   (ar
r : Array PUnit.{u …
-/
theorem mapIdxM'_eq_mapIdxM {α} (f : ℕ → α → m PUnit) (as : List α) :
    mapIdxM' f as = mapIdxM f as *> pure PUnit.unit :=
  mapIdxMAux'_eq_mapIdxMGo f as #[]

end MapIdxM'

end List

