/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Multiset.Powerset

/-!
# The antidiagonal on a multiset.

The antidiagonal of a multiset `s` consists of all pairs `(t₁, t₂)`
such that `t₁ + t₂ = s`. These pairs are counted with multiplicities.
-/

@[expose] public section

assert_not_exists IsOrderedMonoid Ring

universe u

namespace Multiset

open List

variable {α β : Type*}

/-- The antidiagonal of a multiset `s` consists of all pairs `(t₁, t₂)`
    such that `t₁ + t₂ = s`. These pairs are counted with multiplicities. -/
/-
**Multiset.antidiagonal** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：antidiagonal (s : Multiset α) : Multiset (Multiset α × Multiset α)
参数：s : Multiset α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The antidiagonal of a multiset `s` consists of all pairs `(t₁, t₂)`
    such that `t₁ + t₂ = s`. These pairs are counted with multiplicities.
-/
def antidiagonal (s : Multiset α) : Multiset (Multiset α × Multiset α) :=
  Quot.liftOn s (fun l ↦ (revzip (powersetAux l) : Multiset (Multiset α × Multiset α)))
    fun _ _ h ↦ Quot.sound (revzip_powersetAux_perm h)
/-
**Multiset.antidiagonal_coe** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：antidiagonal_coe (l : List α) : @antidiagonal α l = revzip (powersetAux l)
参数：l : List α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem antidiagonal_coe (l : List α) : @antidiagonal α l = revzip (powersetAux l) :=
  rfl

@[simp]
/-
**Multiset.antidiagonal_coe'** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：antidiagonal_coe' (l : List α) : @antidiagonal α l = revzip (powersetAux' 
l)
参数：l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.revzip_powersetAux_perm_aux'`：revzip_powersetAux_perm_aux' {l :
 List α} : revzip (powersetAux l) ~ revzip (powersetAux' l)
-/
theorem antidiagonal_coe' (l : List α) : @antidiagonal α l = revzip (powersetAux' l) :=
  Quot.sound revzip_powersetAux_perm_aux'

/-- A pair `(t₁, t₂)` of multisets is contained in `antidiagonal s`
    if and only if `t₁ + t₂ = s`. -/
@[simp]
/-
**Multiset.mem_antidiagonal** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：mem_antidiagonal {s : Multiset α} {x : Multiset α × Multiset α} : x in ant
idiagonal s ↔ x.1 + x.2 = s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `Multiset.revzip_powersetAux`：revzip_powersetAux {l : List α} ⦃x⦄ (h : x 
in revzip (powersetAux l)) : x.1 + x.2 = ↑l
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.revzip_powersetAux_lemma`：revzip_powersetAux_lemma {α : Type*} 
[DecidableEq α] (l : List α) {l' : List (Multiset α)} (H : forall ⦃x : _ × _⦄, x
 in revzip l' -> x.1 + …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Multiset.le_add_right`：le_add_right (s t : Multiset α) : s <= s + t
· 使用定理 `add_tsub_cancel_left`：add_tsub_cancel_left (a b : α) : a + b - a = b
· 使用定理 `Multiset.instOrderedSub`：∀ {α : Type u_1} [inst : DecidableEq α], Ordere
dSub (Multiset α)

--- 原说明 ---
A pair `(t₁, t₂)` of multisets is contained in `antidiagonal s`
    if and only if `t₁ + t₂ = s`.
-/
theorem mem_antidiagonal {s : Multiset α} {x : Multiset α × Multiset α} :
    x ∈ antidiagonal s ↔ x.1 + x.2 = s :=
  Quotient.inductionOn s fun l ↦ by
    dsimp only [quot_mk_to_coe, antidiagonal_coe]
    refine ⟨fun h => revzip_powersetAux h, fun h ↦ ?_⟩
    have _ := Classical.decEq α
    simp only [revzip_powersetAux_lemma l revzip_powersetAux, h.symm, mem_coe,
      List.mem_map, mem_powersetAux]
    obtain ⟨x₁, x₂⟩ := x
    exact ⟨x₁, le_add_right _ _, by rw [add_tsub_cancel_left x₁ x₂]⟩

@[simp]
/-
**Multiset.antidiagonal_map_fst** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：antidiagonal_map_fst (s : Multiset α) : (antidiagonal s).map Prod.fst = po
werset s
参数：s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.sublists'`：sublists'_nil : sublists' (@nil α) = [[]]
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.antidiagonal_coe'`：antidiagonal_coe' (l : List α) : @antidiagon
al α l = revzip (powersetAux' l)
· 使用定理 `List.revzip_map_fst`：revzip_map_fst (l : List α) : (revzip l).map Prod.f
st = l
· 使用定理 `Multiset.powerset_coe'`：powerset_coe' (l : List α) : @powerset α l = ((s
ublists' l).map (↑) : List (Multiset α))
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem antidiagonal_map_fst (s : Multiset α) : (antidiagonal s).map Prod.fst = powerset s :=
  Quotient.inductionOn s fun l ↦ by simp [powersetAux']

@[simp]
/-
**Multiset.antidiagonal_map_snd** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：antidiagonal_map_snd (s : Multiset α) : (antidiagonal s).map Prod.snd = po
werset s
参数：s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.sublists'`：sublists'_nil : sublists' (@nil α) = [[]]
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.antidiagonal_coe'`：antidiagonal_coe' (l : List α) : @antidiagon
al α l = revzip (powersetAux' l)
· 使用定理 `List.revzip_map_snd`：revzip_map_snd (l : List α) : (revzip l).map Prod.s
nd = l.reverse
· 使用定理 `Multiset.coe_reverse`：coe_reverse (l : List α) : (reverse l : Multiset α
) = l
· 使用定理 `Multiset.powerset_coe'`：powerset_coe' (l : List α) : @powerset α l = ((s
ublists' l).map (↑) : List (Multiset α))
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem antidiagonal_map_snd (s : Multiset α) : (antidiagonal s).map Prod.snd = powerset s :=
  Quotient.inductionOn s fun l ↦ by simp [powersetAux']

@[simp]
/-
**Multiset.antidiagonal_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：antidiagonal_zero : @antidiagonal α 0 = {(0, 0)}
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem antidiagonal_zero : @antidiagonal α 0 = {(0, 0)} :=
  rfl

@[simp]
/-
**Multiset.antidiagonal_cons** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：antidiagonal_cons (a : α) (s) : antidiagonal (a ::ₘ s) = map (Prod.map id 
(cons a)) (antidiagonal s) + map (Prod.map (cons a) id) (antidiagonal s)
参数：a : α；s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.antidiagonal_coe'`：antidiagonal_coe' (l : List α) : @antidiagon
al α l = revzip (powersetAux' l)
· 使用定理 `Multiset.powersetAux'_cons`：∀ {α : Type u_1} (a : α) (l : List α),   Mul
tiset.powersetAux' (a :: l) = Multiset.powersetAux' l ++ List.map (Multiset.cons
 a) (Multiset.po…
· 使用定理 `List.reverse_append`：∀ {α : Type u_1} {as bs : List α}, (as ++ bs).rever
se = bs.reverse ++ as.reverse
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.zip_map`：∀ {α : Type u_1} {γ : Type u_2} {β : Type u_3} {δ : Type u
_4} {f : α → γ} {g : β → δ} {l₁ : List α} {l₂ : List β},   (List.map f l₁).zip (
Li…
· 使用定理 `List.zip_append`：∀ {α : Type u_1} {β : Type u_2} {l₁ r₁ : List α} {l₂ r₂
 : List β},   l₁.length = l₂.length → (l₁ ++ r₁).zip (l₂ ++ r₂) = l₁.zip l₂ ++ r
₁.zip…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `List.length_reverse`：∀ {α : Type u_1} {as : List α}, as.reverse.length =
 as.length
· 使用定理 `List.length_map`：∀ {α : Type u_1} {β : Type u_2} {as : List α} (f : α → 
β), (List.map f as).length = as.length
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `List.map_id_fun`：∀ {α : Type u_1}, List.map id = id
· 使用定理 `List.map_reverse`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l : List 
α}, List.map f l.reverse = (List.map f l).reverse
· 使用定理 `List.Perm.refl`：∀ {α : Type u_1} (l : List α), l.Perm l
-/
theorem antidiagonal_cons (a : α) (s) :
    antidiagonal (a ::ₘ s) =
      map (Prod.map id (cons a)) (antidiagonal s) + map (Prod.map (cons a) id) (antidiagonal s) :=
  Quotient.inductionOn s fun l ↦ by
    simp only [revzip, reverse_append, quot_mk_to_coe, coe_eq_coe, powersetAux'_cons, cons_coe,
      map_coe, antidiagonal_coe', coe_add]
    rw [← zip_map, ← zip_map, zip_append, (_ : _ ++ _ = _)] <;> simp
/-
**Multiset.antidiagonal_add** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：antidiagonal_add (s t : Multiset α) : (s + t).antidiagonal = s.antidiagona
l.bind fun p => t.antidiagonal.map fun q => (p.1 + q.1, p.2 + q.2)
参数：s t : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.zero_add`：∀ {α : Type u_1} (s : Multiset α), 0 + s = s
· 使用定理 `Multiset.singleton_bind`：singleton_bind : bind {a} f = f a
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Prod.mk.eta`：∀ {α : Type u_1} {β : Type u_2} {p : α × β}, (p.1, p.2) = p
· 使用定理 `Multiset.map_id'`：map_id' (s : Multiset α) : map (fun x => x) s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.cons_add`：cons_add (a : α) (s t : Multiset α) : a ::ₘ s + t = a
 ::ₘ (s + t)
· 使用定理 `Multiset.antidiagonal_cons`：antidiagonal_cons (a : α) (s) : antidiagonal
 (a ::ₘ s) = map (Prod.map id (cons a)) (antidiagonal s) + map (Prod.map (cons a
) id) (antidiago…
· 使用定理 `Multiset.add_bind`：add_bind : (s + t).bind f = s.bind f + t.bind f
· 使用定理 `Multiset.bind_map`：bind_map (m : Multiset α) (n : β -> Multiset γ) (f : 
α -> β) : bind (map f m) n = bind m fun a => n (f a)
· 使用定理 `Multiset.map_bind`：map_bind (m : Multiset α) (n : α -> Multiset β) (f : 
β -> γ) : map f (bind m n) = bind m fun a => map f (n a)
· 使用定理 `Multiset.bind_congr`：bind_congr {f g : α -> Multiset β} {m : Multiset α}
 : (forall a in m, f a = g a) -> bind m f = bind m g
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem antidiagonal_add (s t : Multiset α) :
    (s + t).antidiagonal =
      s.antidiagonal.bind fun p ↦ t.antidiagonal.map fun q ↦ (p.1 + q.1, p.2 + q.2) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp_rw [cons_add, antidiagonal_cons, ih, add_bind, bind_map, map_bind, map_map]
    congr! <;> simp

@[simp]
/-
**Multiset.map_swap_antidiagonal** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：map_swap_antidiagonal (s : Multiset α) : s.antidiagonal.map Prod.swap = s.
antidiagonal
参数：s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Multiset.antidiagonal_cons`：antidiagonal_cons (a : α) (s) : antidiagonal
 (a ::ₘ s) = map (Prod.map id (cons a)) (antidiagonal s) + map (Prod.map (cons a
) id) (antidiago…
· 使用定理 `Multiset.map_add`：map_add (f : α -> β) (s t) : map f (s + t) = map f s +
 map f t
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_swap_antidiagonal (s : Multiset α) :
    s.antidiagonal.map Prod.swap = s.antidiagonal := by
  induction s using Multiset.induction_on with
  | empty => rfl
  | cons a s ih =>
    simp only [antidiagonal_cons, map_add, map_map, ← Prod.map_comp_swap,
      ← Multiset.map_map _ Prod.swap, ih, add_comm]
/-
**Multiset.antidiagonal_eq_map_powerset** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：antidiagonal_eq_map_powerset [DecidableEq α] (s : Multiset α) : s.antidiag
onal = s.powerset.map fun t => (s - t, t)
参数：s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Multiset.zero_sub`：∀ {α : Type u_1} [inst : DecidableEq α] (t : Multiset
 α), 0 - t = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Multiset.antidiagonal_cons`：antidiagonal_cons (a : α) (s) : antidiagonal
 (a ::ₘ s) = map (Prod.map id (cons a)) (antidiagonal s) + map (Prod.map (cons a
) id) (antidiago…
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Multiset.powerset_cons`：powerset_cons (a : α) (s) : powerset (a ::ₘ s) =
 powerset s + map (cons a) (powerset s)
· 使用定理 `Multiset.map_add`：map_add (f : α -> β) (s t) : map f (s + t) = map f s +
 map f t
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用引理 `Multiset.sub_cons`：sub_cons (a : α) (s t : Multiset α) : s - a ::ₘ t = s
.erase a - t
· 使用定理 `Multiset.erase_cons_head`：erase_cons_head (a : α) (s : Multiset α) : (a 
::ₘ s).erase a = s
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `Multiset.cons_sub_of_le`：cons_sub_of_le (a : α) {s t : Multiset α} (h : 
t <= s) : a ::ₘ s - t = a ::ₘ (s - t)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_powerset`：mem_powerset {s t : Multiset α} : s in powerset t
 ↔ s <= t
-/
theorem antidiagonal_eq_map_powerset [DecidableEq α] (s : Multiset α) :
    s.antidiagonal = s.powerset.map fun t ↦ (s - t, t) := by
  induction s using Multiset.induction_on with
  | empty => simp only [antidiagonal_zero, powerset_zero, Multiset.zero_sub, map_singleton]
  | cons a s hs =>
    simp_rw [antidiagonal_cons, powerset_cons, map_add, hs, map_map, Function.comp, Prod.map_apply,
      id, sub_cons, erase_cons_head]
    rw [add_comm]
    congr 1
    refine Multiset.map_congr rfl fun x hx ↦ ?_
    rw [cons_sub_of_le _ (mem_powerset.mp hx)]

@[simp]
/-
**Multiset.card_antidiagonal** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：card_antidiagonal (s : Multiset α) : card (antidiagonal s) = 2 ^ card s
参数：s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.card_powerset`：card_powerset (s : Multiset α) : card (powerset 
s) = 2 ^ card s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.card_map`：card_map (f : α -> β) (s) : card (map f s) = card s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.antidiagonal_map_fst`：antidiagonal_map_fst (s : Multiset α) : (
antidiagonal s).map Prod.fst = powerset s
-/
theorem card_antidiagonal (s : Multiset α) : card (antidiagonal s) = 2 ^ card s := by
  have := card_powerset s
  rwa [← antidiagonal_map_fst, card_map] at this

end Multiset

