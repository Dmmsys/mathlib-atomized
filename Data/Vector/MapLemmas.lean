/-
Copyright (c) 2023 Alex Keizer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Keizer
-/
module

public import Mathlib.Data.Vector.Basic
public import Mathlib.Data.Vector.Snoc

/-!
  This file establishes a set of normalization lemmas for `map`/`mapAccumr` operations on vectors
-/

public section

variable {α β γ ζ σ σ₁ σ₂ φ : Type*} {n : ℕ} {s : σ} {s₁ : σ₁} {s₂ : σ₂}

namespace List
namespace Vector

/-!
## Fold nested `mapAccumr`s into one
-/
section Fold

section Unary
variable (xs : Vector α n) (f₁ : β → σ₁ → σ₁ × γ) (f₂ : α → σ₂ → σ₂ × β)

@[simp]
/-
**List.Vector.mapAccumr_mapAccumr** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：mapAccumr_mapAccumr : mapAccumr f₁ (mapAccumr f₂ xs s₂).snd s₁ = let m
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.Vector.mapAccumr_snoc`：mapAccumr_snoc {f : α -> σ -> σ × β} {s : σ}
 : mapAccumr f (xs.snoc x) s = let q
-/
theorem mapAccumr_mapAccumr :
    mapAccumr f₁ (mapAccumr f₂ xs s₂).snd s₁
    = let m := (mapAccumr (fun x s =>
        let r₂ := f₂ x s.snd
        let r₁ := f₁ r₂.snd s.fst
        ((r₁.fst, r₂.fst), r₁.snd)
      ) xs (s₁, s₂))
      (m.fst.fst, m.snd) := by
  induction xs using Vector.revInductionOn generalizing s₁ s₂ <;> simp_all

@[simp]
/-
**List.Vector.mapAccumr_map** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：mapAccumr_map {s : σ₁} (f₂ : α -> β) : (mapAccumr f₁ (map f₂ xs) s) = (map
Accumr (fun x s => f₁ (f₂ x) s) xs s)
参数：f₂ : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.Vector.map_snoc`：map_snoc {f : α -> β} : map f (xs.snoc x) = (map f
 xs).snoc (f x)
· 使用定理 `List.Vector.mapAccumr_snoc`：mapAccumr_snoc {f : α -> σ -> σ × β} {s : σ}
 : mapAccumr f (xs.snoc x) s = let q
-/
theorem mapAccumr_map {s : σ₁} (f₂ : α → β) :
    (mapAccumr f₁ (map f₂ xs) s) = (mapAccumr (fun x s => f₁ (f₂ x) s) xs s) := by
  induction xs using Vector.revInductionOn generalizing s <;> simp_all

@[simp]
/-
**List.Vector.map_mapAccumr** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：map_mapAccumr {s : σ₂} (f₁ : β -> γ) : (map f₁ (mapAccumr f₂ xs s).snd) = 
(mapAccumr (fun x s => let r
参数：f₁ : β -> γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.Vector.mapAccumr_snoc`：mapAccumr_snoc {f : α -> σ -> σ × β} {s : σ}
 : mapAccumr f (xs.snoc x) s = let q
· 使用定理 `List.Vector.map_snoc`：map_snoc {f : α -> β} : map f (xs.snoc x) = (map f
 xs).snoc (f x)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem map_mapAccumr {s : σ₂} (f₁ : β → γ) :
    (map f₁ (mapAccumr f₂ xs s).snd) = (mapAccumr (fun x s =>
        let r := (f₂ x s); (r.fst, f₁ r.snd)
      ) xs s).snd := by
  induction xs using Vector.revInductionOn generalizing s <;> simp_all

@[simp]
/-
**List.Vector.map_map** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：map_map (f₁ : β -> γ) (f₂ : α -> β) : map f₁ (map f₂ xs) = map (fun x => f
₁ <| f₂ x) xs
参数：f₁ : β -> γ；f₂ : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.Vector.map_cons`：∀ {α : Type u_1} {β : Type u_2} {n : ℕ} (f : α → β
) (a : α) (v : List.Vector α n),   List.Vector.map f (a ::ᵥ v) = f a ::ᵥ List.Ve
ctor.map f…
-/
theorem map_map (f₁ : β → γ) (f₂ : α → β) :
    map f₁ (map f₂ xs) = map (fun x => f₁ <| f₂ x) xs := by
  induction xs <;> simp_all
/-
**List.Vector.map_pmap** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：map_pmap {p : α -> Prop} (f₁ : β -> γ) (f₂ : (a : α) -> p a -> β) (H : for
all x in xs.toList, p x) : map f₁ (pmap f₂ xs H) = pmap (fun x hx => f₁ <| f₂ x 
hx) xs H
参数：f₁ : β -> γ；f₂ : (a : α) -> p a -> β；H : forall x in xs.toList, p x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.Vector.toList_cons`：toList_cons (a : α) (v : Vector α n) : toList (
cons a v) = a :: toList v
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `List.Vector.map_cons`：∀ {α : Type u_1} {β : Type u_2} {n : ℕ} (f : α → β
) (a : α) (v : List.Vector α n),   List.Vector.map f (a ::ᵥ v) = f a ::ᵥ List.Ve
ctor.map f…
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
-/
theorem map_pmap {p : α → Prop} (f₁ : β → γ) (f₂ : (a : α) → p a → β) (H : ∀ x ∈ xs.toList, p x) :
    map f₁ (pmap f₂ xs H) = pmap (fun x hx => f₁ <| f₂ x hx) xs H := by
  induction xs <;> simp_all
/-
**List.Vector.pmap_map** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：pmap_map {p : β -> Prop} (f₁ : (b : β) -> p b -> γ) (f₂ : α -> β) (H : for
all x in (xs.map f₂).toList, p x) : pmap f₁ (map f₂ xs) H = pmap (fun x hx => f₁
 (f₂ x) hx) xs (by simpa using H)
参数：f₁ : (b : β) -> p b -> γ；f₂ : α -> β；H : forall x in (xs.map f₂).toList, p x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.Vector.map_cons`：∀ {α : Type u_1} {β : Type u_2} {n : ℕ} (f : α → β
) (a : α) (v : List.Vector α n),   List.Vector.map f (a ::ᵥ v) = f a ::ᵥ List.Ve
ctor.map f…
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.Vector.toList_map`：toList_map {β : Type*} (v : Vector α n) (f : α -
> β) : (v.map f).toList = v.toList.map f
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `List.Vector.toList_cons`：toList_cons (a : α) (v : Vector α n) : toList (
cons a v) = a :: toList v
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `List.Vector.pmap.congr_simp`：∀ {α : Type u_1} {β : Type u_2} {n : ℕ} {p 
: α → Prop} (f f_1 : (a : α) → p a → β),   f = f_1 →     ∀ (v v_1 : List.Vector 
α n) (e_v : v = v…
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
-/
theorem pmap_map {p : β → Prop} (f₁ : (b : β) → p b → γ) (f₂ : α → β)
    (H : ∀ x ∈ (xs.map f₂).toList, p x) :
    pmap f₁ (map f₂ xs) H = pmap (fun x hx => f₁ (f₂ x) hx) xs (by simpa using H) := by
  induction xs <;> simp_all

end Unary

section Binary
variable (xs : Vector α n) (ys : Vector β n)

@[simp]
/-
**List.Vector.mapAccumr** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：mapAccumr (f : α -> σ -> σ × β) : Vector α n -> σ -> σ × Vector β n | ⟨x, 
px⟩, c => let res
参数：f : α -> σ -> σ × β。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapAccumr₂_mapAccumr_left (f₁ : γ → β → σ₁ → σ₁ × ζ) (f₂ : α → σ₂ → σ₂ × γ) :
    (mapAccumr₂ f₁ (mapAccumr f₂ xs s₂).snd ys s₁)
    = let m := (mapAccumr₂ (fun x y s =>
          let r₂ := f₂ x s.snd
          let r₁ := f₁ r₂.snd y s.fst
          ((r₁.fst, r₂.fst), r₁.snd)
        ) xs ys (s₁, s₂))
      (m.fst.fst, m.snd) := by
  induction xs, ys using Vector.revInductionOn₂ generalizing s₁ s₂ <;> simp_all

@[simp]
/-
**List.Vector.map** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → {n : ℕ} → (α → β) → List.Vector α n → Li
st.Vector β n
参数：α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map₂_map_left (f₁ : γ → β → ζ) (f₂ : α → γ) :
    map₂ f₁ (map f₂ xs) ys = map₂ (fun x y => f₁ (f₂ x) y) xs ys := by
  induction xs, ys using Vector.revInductionOn₂ <;> simp_all

@[simp]
/-
**List.Vector.mapAccumr** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：mapAccumr (f : α -> σ -> σ × β) : Vector α n -> σ -> σ × Vector β n | ⟨x, 
px⟩, c => let res
参数：f : α -> σ -> σ × β。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapAccumr₂_mapAccumr_right (f₁ : α → γ → σ₁ → σ₁ × ζ) (f₂ : β → σ₂ → σ₂ × γ) :
    (mapAccumr₂ f₁ xs (mapAccumr f₂ ys s₂).snd s₁)
    = let m := (mapAccumr₂ (fun x y s =>
          let r₂ := f₂ y s.snd
          let r₁ := f₁ x r₂.snd s.fst
          ((r₁.fst, r₂.fst), r₁.snd)
        ) xs ys (s₁, s₂))
      (m.fst.fst, m.snd) := by
  induction xs, ys using Vector.revInductionOn₂ generalizing s₁ s₂ <;> simp_all

@[simp]
/-
**List.Vector.map** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → {n : ℕ} → (α → β) → List.Vector α n → Li
st.Vector β n
参数：α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map₂_map_right (f₁ : α → γ → ζ) (f₂ : β → γ) :
    map₂ f₁ xs (map f₂ ys) = map₂ (fun x y => f₁ x (f₂ y)) xs ys := by
  induction xs, ys using Vector.revInductionOn₂ <;> simp_all

@[simp]
/-
**List.Vector.mapAccumr_mapAccumr** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：mapAccumr_mapAccumr : mapAccumr f₁ (mapAccumr f₂ xs s₂).snd s₁ = let m
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.Vector.mapAccumr_snoc`：mapAccumr_snoc {f : α -> σ -> σ × β} {s : σ}
 : mapAccumr f (xs.snoc x) s = let q
-/
theorem mapAccumr_mapAccumr₂ (f₁ : γ → σ₁ → σ₁ × ζ) (f₂ : α → β → σ₂ → σ₂ × γ) :
    (mapAccumr f₁ (mapAccumr₂ f₂ xs ys s₂).snd s₁)
    = let m := mapAccumr₂ (fun x y s =>
          let r₂ := f₂ x y s.snd
          let r₁ := f₁ r₂.snd s.fst
          ((r₁.fst, r₂.fst), r₁.snd)
        ) xs ys (s₁, s₂)
      (m.fst.fst, m.snd) := by
  induction xs, ys using Vector.revInductionOn₂ generalizing s₁ s₂ <;> simp_all

@[simp]
/-
**List.Vector.map_map** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：map_map (f₁ : β -> γ) (f₂ : α -> β) : map f₁ (map f₂ xs) = map (fun x => f
₁ <| f₂ x) xs
参数：f₁ : β -> γ；f₂ : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.Vector.map_cons`：∀ {α : Type u_1} {β : Type u_2} {n : ℕ} (f : α → β
) (a : α) (v : List.Vector α n),   List.Vector.map f (a ::ᵥ v) = f a ::ᵥ List.Ve
ctor.map f…
-/
theorem map_map₂ (f₁ : γ → ζ) (f₂ : α → β → γ) :
    map f₁ (map₂ f₂ xs ys) = map₂ (fun x y => f₁ <| f₂ x y) xs ys := by
  induction xs, ys using Vector.revInductionOn₂ <;> simp_all

@[simp]
/-
**List.Vector.mapAccumr** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：mapAccumr (f : α -> σ -> σ × β) : Vector α n -> σ -> σ × Vector β n | ⟨x, 
px⟩, c => let res
参数：f : α -> σ -> σ × β。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapAccumr₂_mapAccumr₂_left_left (f₁ : γ → α → σ₁ → σ₁ × φ) (f₂ : α → β → σ₂ → σ₂ × γ) :
    (mapAccumr₂ f₁ (mapAccumr₂ f₂ xs ys s₂).snd xs s₁)
    = let m := mapAccumr₂ (fun x y (s₁, s₂) =>
                let r₂ := f₂ x y s₂
                let r₁ := f₁ r₂.snd x s₁
                ((r₁.fst, r₂.fst), r₁.snd)
              )
            xs ys (s₁, s₂)
    (m.fst.fst, m.snd) := by
  induction xs, ys using Vector.revInductionOn₂ generalizing s₁ s₂ <;> simp_all

@[simp]
/-
**List.Vector.mapAccumr** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：mapAccumr (f : α -> σ -> σ × β) : Vector α n -> σ -> σ × Vector β n | ⟨x, 
px⟩, c => let res
参数：f : α -> σ -> σ × β。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapAccumr₂_mapAccumr₂_left_right
    (f₁ : γ → β → σ₁ → σ₁ × φ) (f₂ : α → β → σ₂ → σ₂ × γ) :
    (mapAccumr₂ f₁ (mapAccumr₂ f₂ xs ys s₂).snd ys s₁)
    = let m := mapAccumr₂ (fun x y (s₁, s₂) =>
                let r₂ := f₂ x y s₂
                let r₁ := f₁ r₂.snd y s₁
                ((r₁.fst, r₂.fst), r₁.snd)
              )
            xs ys (s₁, s₂)
    (m.fst.fst, m.snd) := by
  induction xs, ys using Vector.revInductionOn₂ generalizing s₁ s₂ <;> simp_all

@[simp]
/-
**List.Vector.mapAccumr** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：mapAccumr (f : α -> σ -> σ × β) : Vector α n -> σ -> σ × Vector β n | ⟨x, 
px⟩, c => let res
参数：f : α -> σ -> σ × β。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapAccumr₂_mapAccumr₂_right_left (f₁ : α → γ → σ₁ → σ₁ × φ) (f₂ : α → β → σ₂ → σ₂ × γ) :
    (mapAccumr₂ f₁ xs (mapAccumr₂ f₂ xs ys s₂).snd s₁)
    = let m := mapAccumr₂ (fun x y (s₁, s₂) =>
                let r₂ := f₂ x y s₂
                let r₁ := f₁ x r₂.snd s₁
                ((r₁.fst, r₂.fst), r₁.snd)
              )
            xs ys (s₁, s₂)
    (m.fst.fst, m.snd) := by
  induction xs, ys using Vector.revInductionOn₂ generalizing s₁ s₂ <;> simp_all

@[simp]
/-
**List.Vector.mapAccumr** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：mapAccumr (f : α -> σ -> σ × β) : Vector α n -> σ -> σ × Vector β n | ⟨x, 
px⟩, c => let res
参数：f : α -> σ -> σ × β。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapAccumr₂_mapAccumr₂_right_right (f₁ : β → γ → σ₁ → σ₁ × φ) (f₂ : α → β → σ₂ → σ₂ × γ) :
    (mapAccumr₂ f₁ ys (mapAccumr₂ f₂ xs ys s₂).snd s₁)
    = let m := mapAccumr₂ (fun x y (s₁, s₂) =>
                let r₂ := f₂ x y s₂
                let r₁ := f₁ y r₂.snd s₁
                ((r₁.fst, r₂.fst), r₁.snd)
              )
            xs ys (s₁, s₂)
    (m.fst.fst, m.snd) := by
  induction xs, ys using Vector.revInductionOn₂ generalizing s₁ s₂ <;> simp_all

end Binary

end Fold

/-!
## Bisimulations
We can prove two applications of `mapAccumr` equal by providing a bisimulation relation that relates
the initial states.

That is, by providing a relation `R : σ₁ → σ₁ → Prop` such that `R s₁ s₂` implies that `R` also
relates any pair of states reachable by applying `f₁` to `s₁` and `f₂` to `s₂`, with any possible
input values.
-/

section Bisim
variable {xs : Vector α n}

/-
**List.Vector.mapAccumr_bisim** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：mapAccumr_bisim {f₁ : α -> σ₁ -> σ₁ × β} {f₂ : α -> σ₂ -> σ₂ × β} {s₁ : σ₁
} {s₂ : σ₂} (R : σ₁ -> σ₂ -> Prop) (h₀ : R s₁ s₂) (hR : forall {s q} a, R s q ->
 R (f₁ a s).1 (f₂ a q).1 ∧ (f₁ a s).2 = (f₂ a q).2) : R (mapAccumr f₁ xs s₁).fst
 (mapAccumr f₂ xs s₂).fst ∧ (mapAccumr f₁ xs s₁).snd = (mapAccumr f₂ xs s₂).snd
参数：R : σ₁ -> σ₂ -> Prop；h₀ : R s₁ s₂；hR : forall {s q} a, R s q -> R (f₁ a s).1 
(f₂ a q).1 ∧ (f₁ a s).2 = (f₂ a q).2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.Vector.mapAccumr_snoc`：mapAccumr_snoc {f : α -> σ -> σ × β} {s : σ}
 : mapAccumr f (xs.snoc x) s = let q
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
theorem mapAccumr_bisim {f₁ : α → σ₁ → σ₁ × β} {f₂ : α → σ₂ → σ₂ × β} {s₁ : σ₁} {s₂ : σ₂}
    (R : σ₁ → σ₂ → Prop) (h₀ : R s₁ s₂)
    (hR : ∀ {s q} a, R s q → R (f₁ a s).1 (f₂ a q).1 ∧ (f₁ a s).2 = (f₂ a q).2) :
    R (mapAccumr f₁ xs s₁).fst (mapAccumr f₂ xs s₂).fst
    ∧ (mapAccumr f₁ xs s₁).snd = (mapAccumr f₂ xs s₂).snd := by
  induction xs using Vector.revInductionOn generalizing s₁ s₂
  next => exact ⟨h₀, rfl⟩
  next xs x ih =>
    rcases (hR x h₀) with ⟨hR, _⟩
    simp only [mapAccumr_snoc, ih hR, true_and]
    congr 1
/-
**List.Vector.mapAccumr_bisim_tail** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：mapAccumr_bisim_tail {f₁ : α -> σ₁ -> σ₁ × β} {f₂ : α -> σ₂ -> σ₂ × β} {s₁
 : σ₁} {s₂ : σ₂} (h : exists R : σ₁ -> σ₂ -> Prop, R s₁ s₂ ∧ forall {s q} a, R s
 q -> R (f₁ a s).1 (f₂ a q).1 ∧ (f₁ a s).2 = (f₂ a q).2) : (mapAccumr f₁ xs s₁).
snd = (mapAccumr f₂ xs s₂).snd
参数：h : exists R : σ₁ -> σ₂ -> Prop, R s₁ s₂ ∧ forall {s q} a, R s q -> R (f₁ a s
).1 (f₂ a q).1 ∧ (f₁ a s).2 = (f₂ a q).2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `List.Vector.mapAccumr_bisim`：mapAccumr_bisim {f₁ : α -> σ₁ -> σ₁ × β} {f
₂ : α -> σ₂ -> σ₂ × β} {s₁ : σ₁} {s₂ : σ₂} (R : σ₁ -> σ₂ -> Prop) (h₀ : R s₁ s₂)
 (hR : forall {s …
-/
theorem mapAccumr_bisim_tail {f₁ : α → σ₁ → σ₁ × β} {f₂ : α → σ₂ → σ₂ × β} {s₁ : σ₁} {s₂ : σ₂}
    (h : ∃ R : σ₁ → σ₂ → Prop, R s₁ s₂ ∧
      ∀ {s q} a, R s q → R (f₁ a s).1 (f₂ a q).1 ∧ (f₁ a s).2 = (f₂ a q).2) :
    (mapAccumr f₁ xs s₁).snd = (mapAccumr f₂ xs s₂).snd := by
  rcases h with ⟨R, h₀, hR⟩
  exact (mapAccumr_bisim R h₀ hR).2
/-
**List.Vector.mapAccumr** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：mapAccumr (f : α -> σ -> σ × β) : Vector α n -> σ -> σ × Vector β n | ⟨x, 
px⟩, c => let res
参数：f : α -> σ -> σ × β。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapAccumr₂_bisim {ys : Vector β n} {f₁ : α → β → σ₁ → σ₁ × γ}
    {f₂ : α → β → σ₂ → σ₂ × γ} {s₁ : σ₁} {s₂ : σ₂}
    (R : σ₁ → σ₂ → Prop) (h₀ : R s₁ s₂)
    (hR : ∀ {s q} a b, R s q → R (f₁ a b s).1 (f₂ a b q).1 ∧ (f₁ a b s).2 = (f₂ a b q).2) :
    R (mapAccumr₂ f₁ xs ys s₁).1 (mapAccumr₂ f₂ xs ys s₂).1
    ∧ (mapAccumr₂ f₁ xs ys s₁).2 = (mapAccumr₂ f₂ xs ys s₂).2 := by
  induction xs, ys using Vector.revInductionOn₂ generalizing s₁ s₂
  next => exact ⟨h₀, rfl⟩
  next xs ys x y ih =>
    rcases (hR x y h₀) with ⟨hR, _⟩
    simp only [mapAccumr₂_snoc, ih hR, true_and]
    congr 1
/-
**List.Vector.mapAccumr** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：mapAccumr (f : α -> σ -> σ × β) : Vector α n -> σ -> σ × Vector β n | ⟨x, 
px⟩, c => let res
参数：f : α -> σ -> σ × β。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapAccumr₂_bisim_tail {ys : Vector β n} {f₁ : α → β → σ₁ → σ₁ × γ}
    {f₂ : α → β → σ₂ → σ₂ × γ} {s₁ : σ₁} {s₂ : σ₂}
    (h : ∃ R : σ₁ → σ₂ → Prop, R s₁ s₂ ∧
      ∀ {s q} a b, R s q → R (f₁ a b s).1 (f₂ a b q).1 ∧ (f₁ a b s).2 = (f₂ a b q).2) :
    (mapAccumr₂ f₁ xs ys s₁).2 = (mapAccumr₂ f₂ xs ys s₂).2 := by
  rcases h with ⟨R, h₀, hR⟩
  exact (mapAccumr₂_bisim R h₀ hR).2

end Bisim

/-!
## Redundant state optimization

The following section are collection of rewrites to simplify, or even get rid, redundant
accumulation state
-/
section RedundantState
variable {xs : Vector α n} {ys : Vector β n}

/-
**List.Vector.map_eq_mapAccumr** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {n : ℕ} {xs : List.Vector α n} {f : α → β}
,   List.Vector.map f xs = (List.Vector.mapAccumr (fun x x_1 => ((), f x)) xs ()
).2
参数：List.Vector.mapAccumr (fun x x_1 => ((), f x)) xs ()。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.Vector.map_snoc`：map_snoc {f : α -> β} : map f (xs.snoc x) = (map f
 xs).snoc (f x)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.Vector.mapAccumr_snoc`：mapAccumr_snoc {f : α -> σ -> σ × β} {s : σ}
 : mapAccumr f (xs.snoc x) s = let q
-/
protected theorem map_eq_mapAccumr {f : α → β} :
    map f xs = (mapAccumr (fun x (_ : Unit) ↦ ((), f x)) xs ()).snd := by
  induction xs using Vector.revInductionOn <;> simp_all

/--
If there is a set of states that is closed under `f`, and such that `f` produces that same output
for all states in this set, then the state is not actually needed.
Hence, then we can rewrite `mapAccumr` into just `map`.
-/
/-
**List.Vector.mapAccumr_eq_map** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：mapAccumr_eq_map {f : α -> σ -> σ × β} {s₀ : σ} (S : Set σ) (h₀ : s₀ in S)
 (closure : forall a s, s in S -> (f a s).1 in S) (out : forall a s s', s in S -
> s' in S -> (f a s).2 = (f a s').2) : (mapAccumr f xs s₀).snd = map (f · s₀ |>.
snd) xs
参数：S : Set σ；h₀ : s₀ in S；closure : forall a s, s in S -> (f a s).1 in S；out : f
orall a s s', s in S -> s' in S -> (f a s).2 = (f a s').2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.Vector.map_eq_mapAccumr`：∀ {α : Type u_1} {β : Type u_2} {n : ℕ} {x
s : List.Vector α n} {f : α → β},   List.Vector.map f xs = (List.Vector.mapAccum
r (fun x x_1 => ((…
· 使用定理 `List.Vector.mapAccumr_bisim_tail`：mapAccumr_bisim_tail {f₁ : α -> σ₁ -> 
σ₁ × β} {f₂ : α -> σ₂ -> σ₂ × β} {s₁ : σ₁} {s₂ : σ₂} (h : exists R : σ₁ -> σ₂ ->
 Prop, R s₁ s₂ ∧ foral…

--- 原说明 ---
If there is a set of states that is closed under `f`, and such that `f` produces
 that same output
for all states in this set, then the state is not actually needed.
Hence, then we can rewrite `mapAccumr` into just `map`.
-/
theorem mapAccumr_eq_map {f : α → σ → σ × β} {s₀ : σ} (S : Set σ) (h₀ : s₀ ∈ S)
    (closure : ∀ a s, s ∈ S → (f a s).1 ∈ S)
    (out : ∀ a s s', s ∈ S → s' ∈ S → (f a s).2 = (f a s').2) :
    (mapAccumr f xs s₀).snd = map (f · s₀ |>.snd) xs := by
  rw [Vector.map_eq_mapAccumr]
  apply mapAccumr_bisim_tail
  use fun s _ => s ∈ S, h₀
  exact @fun s _q a h => ⟨closure a s h, out a s s₀ h h₀⟩
/-
**List.Vector.map** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → {n : ℕ} → (α → β) → List.Vector α n → Li
st.Vector β n
参数：α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem map₂_eq_mapAccumr₂ {f : α → β → γ} :
    map₂ f xs ys = (mapAccumr₂ (fun x y (_ : Unit) ↦ ((), f x y)) xs ys ()).snd := by
  induction xs, ys using Vector.revInductionOn₂ <;> simp_all

/--
If there is a set of states that is closed under `f`, and such that `f` produces that same output
for all states in this set, then the state is not actually needed.
Hence, then we can rewrite `mapAccumr₂` into just `map₂`.
-/
/-
**List.Vector.mapAccumr** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：mapAccumr (f : α -> σ -> σ × β) : Vector α n -> σ -> σ × Vector β n | ⟨x, 
px⟩, c => let res
参数：f : α -> σ -> σ × β。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If there is a set of states that is closed under `f`, and such that `f` produces
 that same output
for all states in this set, then the state is not actually needed.
Hence, then we can rewrite `mapAccumr₂` into just `map₂`.
-/
theorem mapAccumr₂_eq_map₂ {f : α → β → σ → σ × γ} {s₀ : σ} (S : Set σ) (h₀ : s₀ ∈ S)
    (closure : ∀ a b s, s ∈ S → (f a b s).1 ∈ S)
    (out : ∀ a b s s', s ∈ S → s' ∈ S → (f a b s).2 = (f a b s').2) :
    (mapAccumr₂ f xs ys s₀).snd = map₂ (f · · s₀ |>.snd) xs ys := by
  rw [Vector.map₂_eq_mapAccumr₂]
  apply mapAccumr₂_bisim_tail
  use fun s _ => s ∈ S, h₀
  exact @fun s _q a b h => ⟨closure a b s h, out a b s s₀ h h₀⟩

/--
If an accumulation function `f`, given an initial state `s`, produces `s` as its output state
for all possible input bits, then the state is redundant and can be optimized out.
-/
@[simp]
/-
**List.Vector.mapAccumr_eq_map_of_constant_state** 是 Mathlib 中的一个定理，位于命名空间 `List
.Vector`。
形式化陈述：mapAccumr_eq_map_of_constant_state (f : α -> σ -> σ × β) (s : σ) (h : fora
ll a, (f a s).fst = s) : mapAccumr f xs s = (s, (map (fun x => (f x s).snd) xs))
参数：f : α -> σ -> σ × β；s : σ；h : forall a, (f a s).fst = s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.Vector.mapAccumr_snoc`：mapAccumr_snoc {f : α -> σ -> σ × β} {s : σ}
 : mapAccumr f (xs.snoc x) s = let q
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.Vector.map_snoc`：map_snoc {f : α -> β} : map f (xs.snoc x) = (map f
 xs).snoc (f x)

--- 原说明 ---
If an accumulation function `f`, given an initial state `s`, produces `s` as its
 output state
for all possible input bits, then the state is redundant and can be optimized ou
t.
-/
theorem mapAccumr_eq_map_of_constant_state (f : α → σ → σ × β) (s : σ) (h : ∀ a, (f a s).fst = s) :
    mapAccumr f xs s = (s, (map (fun x => (f x s).snd) xs)) := by
  induction xs using revInductionOn <;> simp_all

/--
If an accumulation function `f`, given an initial state `s`, produces `s` as its output state
for all possible input bits, then the state is redundant and can be optimized out.
-/
@[simp]
/-
**List.Vector.mapAccumr** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：mapAccumr (f : α -> σ -> σ × β) : Vector α n -> σ -> σ × Vector β n | ⟨x, 
px⟩, c => let res
参数：f : α -> σ -> σ × β。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If an accumulation function `f`, given an initial state `s`, produces `s` as its
 output state
for all possible input bits, then the state is redundant and can be optimized ou
t.
-/
theorem mapAccumr₂_eq_map₂_of_constant_state (f : α → β → σ → σ × γ) (s : σ)
    (h : ∀ a b, (f a b s).fst = s) :
    mapAccumr₂ f xs ys s = (s, (map₂ (fun x y => (f x y s).snd) xs ys)) := by
  induction xs, ys using revInductionOn₂ <;> simp_all

/--
If an accumulation function `f`, produces the same output bits regardless of accumulation state,
then the state is redundant and can be optimized out.
-/
@[simp]
/-
**List.Vector.mapAccumr_eq_map_of_unused_state** 是 Mathlib 中的一个定理，位于命名空间 `List.V
ector`。
形式化陈述：mapAccumr_eq_map_of_unused_state (f : α -> σ -> σ × β) (f' : α -> β) (s : 
σ) (h : forall a s, (f a s).snd = f' a) : (mapAccumr f xs s).snd = (map f' xs)
参数：f : α -> σ -> σ × β；f' : α -> β；s : σ；h : forall a s, (f a s).snd = f' a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.Vector.mapAccumr_eq_map`：mapAccumr_eq_map {f : α -> σ -> σ × β} {s₀
 : σ} (S : Set σ) (h₀ : s₀ in S) (closure : forall a s, s in S -> (f a s).1 in S
) (out : forall a …
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If an accumulation function `f`, produces the same output bits regardless of acc
umulation state,
then the state is redundant and can be optimized out.
-/
theorem mapAccumr_eq_map_of_unused_state (f : α → σ → σ × β) (f' : α → β) (s : σ)
    (h : ∀ a s, (f a s).snd = f' a) :
    (mapAccumr f xs s).snd = (map f' xs) := by
  rw [mapAccumr_eq_map Set.univ (Set.mem_univ _) (fun _ _ _ => Set.mem_univ _)
    (fun a s s' _ _ => by rw [h, h])]
  simp_all

/--
If an accumulation function `f`, produces the same output bits regardless of accumulation state,
then the state is redundant and can be optimized out.
-/
@[simp]
/-
**List.Vector.mapAccumr** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：mapAccumr (f : α -> σ -> σ × β) : Vector α n -> σ -> σ × Vector β n | ⟨x, 
px⟩, c => let res
参数：f : α -> σ -> σ × β。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If an accumulation function `f`, produces the same output bits regardless of acc
umulation state,
then the state is redundant and can be optimized out.
-/
theorem mapAccumr₂_eq_map₂_of_unused_state (f : α → β → σ → σ × γ) (f' : α → β → γ) (s : σ)
    (h : ∀ a b s, (f a b s).snd = f' a b) :
    (mapAccumr₂ f xs ys s).snd = (map₂ (fun x y => (f x y s).snd) xs ys) :=
  mapAccumr₂_eq_map₂ .univ (Set.mem_univ _) (fun _ _ _ _ => Set.mem_univ _)
    (fun a b s s' _ _ => by rw [h, h])

/-- If `f` takes a pair of states, but always returns the same value for both elements of the
pair, then we can simplify to just a single element of state.
-/
@[simp]
/-
**List.Vector.mapAccumr_redundant_pair** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：mapAccumr_redundant_pair (f : α -> (σ × σ) -> (σ × σ) × β) (h : forall x s
, (f x (s, s)).fst.fst = (f x (s, s)).fst.snd) : (mapAccumr f xs (s, s)).snd = (
mapAccumr (fun x (s : σ) => (f x (s, s) |>.fst.fst, f x (s, s) |>.snd) ) xs s).s
nd
参数：f : α -> (σ × σ) -> (σ × σ) × β；h : forall x s, (f x (s, s)).fst.fst = (f x (
s, s)).fst.snd。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Vector.mapAccumr_bisim_tail`：mapAccumr_bisim_tail {f₁ : α -> σ₁ -> 
σ₁ × β} {f₂ : α -> σ₂ -> σ₂ × β} {s₁ : σ₁} {s₂ : σ₂} (h : exists R : σ₁ -> σ₂ ->
 Prop, R s₁ s₂ ∧ foral…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
If `f` takes a pair of states, but always returns the same value for both elemen
ts of the
pair, then we can simplify to just a single element of state.
-/
theorem mapAccumr_redundant_pair (f : α → (σ × σ) → (σ × σ) × β)
    (h : ∀ x s, (f x (s, s)).fst.fst = (f x (s, s)).fst.snd) :
    (mapAccumr f xs (s, s)).snd = (mapAccumr (fun x (s : σ) =>
      (f x (s, s) |>.fst.fst, f x (s, s) |>.snd)
    ) xs s).snd :=
  mapAccumr_bisim_tail <| by
    use fun (s₁, s₂) s => s₂ = s ∧ s₁ = s
    simp_all

/-- If `f` takes a pair of states, but always returns the same value for both elements of the
pair, then we can simplify to just a single element of state.
-/
@[simp]
/-
**List.Vector.mapAccumr** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：mapAccumr (f : α -> σ -> σ × β) : Vector α n -> σ -> σ × Vector β n | ⟨x, 
px⟩, c => let res
参数：f : α -> σ -> σ × β。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` takes a pair of states, but always returns the same value for both elemen
ts of the
pair, then we can simplify to just a single element of state.
-/
theorem mapAccumr₂_redundant_pair (f : α → β → (σ × σ) → (σ × σ) × γ)
    (h : ∀ x y s, let s' := (f x y (s, s)).fst; s'.fst = s'.snd) :
    (mapAccumr₂ f xs ys (s, s)).snd = (mapAccumr₂ (fun x y (s : σ) =>
      (f x y (s, s) |>.fst.fst, f x y (s, s) |>.snd)
    ) xs ys s).snd :=
  mapAccumr₂_bisim_tail <| by
    use fun (s₁, s₂) s => s₂ = s ∧ s₁ = s
    simp_all

end RedundantState

/-!
## Unused input optimizations
-/
section UnusedInput
variable {xs : Vector α n} {ys : Vector β n}

/--
If `f` returns the same output and next state for every value of it's first argument, then
`xs : Vector` is ignored, and we can rewrite `mapAccumr₂` into `map`.
-/
@[simp]
/-
**List.Vector.mapAccumr** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：mapAccumr (f : α -> σ -> σ × β) : Vector α n -> σ -> σ × Vector β n | ⟨x, 
px⟩, c => let res
参数：f : α -> σ -> σ × β。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` returns the same output and next state for every value of it's first argu
ment, then
`xs : Vector` is ignored, and we can rewrite `mapAccumr₂` into `map`.
-/
theorem mapAccumr₂_unused_input_left (f : α → β → σ → σ × γ) (f' : β → σ → σ × γ)
    (h : ∀ a b s, f a b s = f' b s) :
    mapAccumr₂ f xs ys s = mapAccumr f' ys s := by
  induction xs, ys using Vector.revInductionOn₂ generalizing s with
  | nil => rfl
  | snoc xs ys x y ih => simp [h x y s, ih]

/--
If `f` returns the same output and next state for every value of it's second argument, then
`ys : Vector` is ignored, and we can rewrite `mapAccumr₂` into `map`.
-/
@[simp]
/-
**List.Vector.mapAccumr** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：mapAccumr (f : α -> σ -> σ × β) : Vector α n -> σ -> σ × Vector β n | ⟨x, 
px⟩, c => let res
参数：f : α -> σ -> σ × β。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` returns the same output and next state for every value of it's second arg
ument, then
`ys : Vector` is ignored, and we can rewrite `mapAccumr₂` into `map`.
-/
theorem mapAccumr₂_unused_input_right (f : α → β → σ → σ × γ) (f' : α → σ → σ × γ)
    (h : ∀ a b s, f a b s = f' a s) :
    mapAccumr₂ f xs ys s = mapAccumr f' xs s := by
  induction xs, ys using Vector.revInductionOn₂ generalizing s with
  | nil => rfl
  | snoc xs ys x y ih => simp [h x y s, ih]

end UnusedInput

/-!
## Commutativity
-/
section Comm
variable (xs ys : Vector α n)

/-
**List.Vector.map** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → {n : ℕ} → (α → β) → List.Vector α n → Li
st.Vector β n
参数：α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map₂_comm (f : α → α → β) (comm : ∀ a₁ a₂, f a₁ a₂ = f a₂ a₁) :
    map₂ f xs ys = map₂ f ys xs := by
  induction xs, ys using Vector.inductionOn₂ <;> simp_all
/-
**List.Vector.mapAccumr** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：mapAccumr (f : α -> σ -> σ × β) : Vector α n -> σ -> σ × Vector β n | ⟨x, 
px⟩, c => let res
参数：f : α -> σ -> σ × β。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapAccumr₂_comm (f : α → α → σ → σ × γ) (comm : ∀ a₁ a₂ s, f a₁ a₂ s = f a₂ a₁ s) :
    mapAccumr₂ f xs ys s = mapAccumr₂ f ys xs s := by
  induction xs, ys using Vector.inductionOn₂ generalizing s <;> simp_all

end Comm

/-!
## Argument Flipping
-/
section Flip
variable (xs : Vector α n) (ys : Vector β n)

/-
**List.Vector.map** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → {n : ℕ} → (α → β) → List.Vector α n → Li
st.Vector β n
参数：α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map₂_flip (f : α → β → γ) :
    map₂ f xs ys = map₂ (flip f) ys xs := by
  induction xs, ys using Vector.inductionOn₂ <;> simp_all [flip]
/-
**List.Vector.mapAccumr** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：mapAccumr (f : α -> σ -> σ × β) : Vector α n -> σ -> σ × Vector β n | ⟨x, 
px⟩, c => let res
参数：f : α -> σ -> σ × β。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapAccumr₂_flip (f : α → β → σ → σ × γ) :
    mapAccumr₂ f xs ys s = mapAccumr₂ (flip f) ys xs s := by
  induction xs, ys using Vector.inductionOn₂ <;> simp_all [flip]

end Flip

end Vector

end List

