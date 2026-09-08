/-
Copyright (c) 2023 Antoine Chambert-Loir and María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández, Eric Wieser, Bhavik Mehta,
  Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Pointwise.Finset.Scalar
public import Mathlib.Data.Fin.Tuple.NatAntidiagonal
public import Mathlib.Data.Finset.Sym
public import Mathlib.Algebra.Group.Pi.Lemmas

/-!
# Antidiagonal of functions as finsets

This file provides the finset of functions summing to a specific value on a finset. Such finsets
should be thought of as the "antidiagonals" in the space of functions.

Precisely, for a commutative monoid `μ` with antidiagonals (see `Finset.HasAntidiagonal`),
`Finset.piAntidiag s n` is the finset of all functions `f : ι → μ` with support contained in `s` and
such that the sum of its values equals `n : μ`.

We define it recursively on `s` using `Finset.HasAntidiagonal.antidiagonal : μ → Finset (μ × μ)`.
Technically, we non-canonically identify `s` with `Fin n` where `n = s.card`, recurse on `n` using
that `(Fin (n + 1) → μ) ≃ (Fin n → μ) × μ`, and show the end result doesn't depend on our
identification. See `Finset.finAntidiag` for the details.

## Main declarations

* `Finset.piAntidiag s n`: Finset of all functions `f : ι → μ` with support contained in `s` and
  such that the sum of its values equals `n : μ`.
* `Finset.finAntidiagonal d n`: Computationally efficient special case of `Finset.piAntidiag` when
  `ι := Fin d`.

## TODO

`Finset.finAntidiagonal` is strictly more general than `Finset.Nat.antidiagonalTuple`. Deduplicate.

## See also

`Finset.finsuppAntidiag` for the `Finset (ι →₀ μ)`-valued version of `Finset.piAntidiag`.
-/

@[expose] public section

open Function

variable {ι μ μ' : Type*}

namespace Finset
section AddCommMonoid
variable [DecidableEq ι] [AddCommMonoid μ] [HasAntidiagonal μ] [DecidableEq μ] {n : μ}

/-!
### `Fin d → μ`

In this section, we define the antidiagonals in `Fin d → μ` by recursion on `d`. Note that this is
computationally efficient, although probably not as efficient as `Finset.Nat.antidiagonalTuple`.
-/

/-- Auxiliary construction for `finAntidiagonal` that bundles a proof of lawfulness
(`mem_finAntidiagonal`), as this is needed to invoke `disjiUnion`. Using `Finset.disjiUnion` makes
this computationally much more efficient than using `Finset.biUnion`. -/
/-
**Finset.finAntidiagonal.aux** 是 Mathlib 中的一个定义，位于命名空间 `Finset.finAntidiagonal`。
形式化陈述：{μ : Type u_2} →   [inst : AddCommMonoid μ] →     [Finset.HasAntidiagonal 
μ] → [DecidableEq μ] → (d : ℕ) → (n : μ) → { s // ∀ (f : Fin d → μ), f ∈ s ↔ ∑ i
, f i = n }
参数：d : ℕ；n : μ；f : Fin d → μ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary construction for `finAntidiagonal` that bundles a proof of lawfulness
(`mem_finAntidiagonal`), as this is needed to invoke `disjiUnion`. Using `Finset
.disjiUnion` makes
this computationally much more efficient than using `Finset.biUnion`.
-/
def finAntidiagonal.aux (d : ℕ) (n : μ) : {s : Finset (Fin d → μ) // ∀ f, f ∈ s ↔ ∑ i, f i = n} :=
  match d with
  | 0 =>
    if h : n = 0 then
      ⟨{0}, by simp [h, Subsingleton.elim _ ![]]⟩
    else
      ⟨∅, by simp [Ne.symm h]⟩
  | d + 1 =>
    { val := (antidiagonal n).disjiUnion
        (fun ab => (aux d ab.2).1.map {
            toFun := Fin.cons (ab.1)
            inj' := Fin.cons_right_injective _ }) <| by
        intro i _ j _ hij
        simp only [Finset.disjoint_left, Finset.mem_map, Embedding.coeFn_mk]
        grind [Fin.cons_inj]
      property := fun f => by
        simp_rw [mem_disjiUnion, mem_antidiagonal, mem_map, Embedding.coeFn_mk, Prod.exists,
          (aux d _).prop, Fin.sum_univ_succ]
        constructor
        · rintro ⟨a, b, rfl, g, rfl, rfl⟩
          simp only [Fin.cons_zero, Fin.cons_succ]
        · intro hf
          exact ⟨_, _, hf, _, rfl, Fin.cons_self_tail f⟩ }

/-- `finAntidiagonal d n` is the type of `d`-tuples with sum `n`.

TODO: deduplicate with the less general `Finset.Nat.antidiagonalTuple`. -/
/-
**Finset.finAntidiagonal** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：finAntidiagonal (d : Nat) (n : μ) : Finset (Fin d -> μ)
参数：d : Nat；n : μ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`finAntidiagonal d n` is the type of `d`-tuples with sum `n`.

TODO: deduplicate with the less general `Finset.Nat.antidiagonalTuple`.
-/
def finAntidiagonal (d : ℕ) (n : μ) : Finset (Fin d → μ) := finAntidiagonal.aux d n
/-
**Finset.mem_finAntidiagonal** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {μ : Type u_2} [inst : AddCommMonoid μ] [inst_1 : Finset.HasAntidiagonal
 μ] [inst_2 : DecidableEq μ] {n : μ} {d : ℕ}   {f : Fin d → μ}, f ∈ Finset.finAn
tidiagonal d n ↔ ∑ i, f i = n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
@[simp] lemma mem_finAntidiagonal {d : ℕ} {f : Fin d → μ} :
    f ∈ finAntidiagonal d n ↔ ∑ i, f i = n := (finAntidiagonal.aux d n).prop f

/-!
### `ι → μ`

In this section, we transfer the antidiagonals in `Fin s.card → μ` to antidiagonals in `ι → s` by
choosing an identification `s ≃ Fin s.card` and proving that the end result does not depend on that
choice.
-/

/-- The finset of functions `ι → μ` with support contained in `s` and sum `n`. -/
/-
**Finset.piAntidiag** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：piAntidiag (s : Finset ι) (n : μ) : Finset (ι -> μ)
参数：s : Finset ι；n : μ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The finset of functions `ι → μ` with support contained in `s` and sum `n`.
-/
def piAntidiag (s : Finset ι) (n : μ) : Finset (ι → μ) := by
  refine (Fintype.truncEquivFinOfCardEq <| Fintype.card_coe s).lift
    (fun e ↦ (finAntidiagonal s.card n).map ⟨fun f i ↦ if hi : i ∈ s then f (e ⟨i, hi⟩) else 0, ?_⟩)
    fun e₁ e₂ ↦ ?_
  · rw [Injective]
    rintro f g hfg
    ext i
    simpa using congr_fun hfg (e.symm i)
  · ext f
    simp only [mem_map, mem_finAntidiagonal]
    refine Equiv.exists_congr ((e₁.symm.trans e₂).arrowCongr <| .refl _) fun g ↦ ?_
    have := Fintype.sum_equiv (e₂.symm.trans e₁) _ g fun _ ↦ rfl
    simp_all

variable {s : Finset ι} {n : μ} {f : ι → μ}
/-
**Finset.mem_piAntidiag** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {ι : Type u_1} {μ : Type u_2} [inst : DecidableEq ι] [inst_1 : AddCommMo
noid μ] [inst_2 : Finset.HasAntidiagonal μ]   [inst_3 : DecidableEq μ] {s : Fins
et ι} {n : μ} {f : ι → μ},   f ∈ s.piAntidiag n ↔ s.sum f = n ∧ ∀ (i : ι), f i ≠
 0 → i ∈ s
参数：i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.piAntidiag.eq_1`：∀ {ι : Type u_1} {μ : Type u_2} [inst : Decidabl
eEq ι] [inst_1 : AddCommMonoid μ] [inst_2 : Finset.HasAntidiagonal μ]   [inst_3 
: DecidableE…
· 使用定理 `Trunc.ind`：ind {β : Trunc α -> Prop} : (forall a : α, β (mk a)) -> foral
l q : Trunc α, β q
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Finset.sum_dite_of_true`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} 
[inst : AddCommMonoid M] {p : ι → Prop} [inst_1 : DecidablePred p]   (h : ∀ i ∈ 
s, p i) (f : …
· 使用定理 `Fintype.sum_equiv`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst 
: Fintype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   (e : ι ≃ κ) (f : 
ι → M) …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Finset.sum_attach`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid
 M] (s : Finset ι) (f : ι → M), ∑ x ∈ s.attach, f ↑x = ∑ x ∈ s, f x
· 使用定理 `Fintype.card_coe`：Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.
card s = #s
-/
@[simp] lemma mem_piAntidiag : f ∈ piAntidiag s n ↔ s.sum f = n ∧ ∀ i, f i ≠ 0 → i ∈ s := by
  rw [piAntidiag]
  induction Fintype.truncEquivFinOfCardEq (Fintype.card_coe s) using Trunc.ind with | _ e
  simp only [Trunc.lift_mk, mem_map, mem_finAntidiagonal, Embedding.coeFn_mk]
  constructor
  · rintro ⟨f, ⟨hf, rfl⟩, rfl⟩
    rw [sum_dite_of_true fun _ ↦ id]
    exact ⟨Fintype.sum_equiv e _ _ (by simp), by simp +contextual⟩
  · rintro ⟨rfl, hf⟩
    refine ⟨f ∘ (↑) ∘ e.symm, ?_, by grind⟩
    rw [← sum_attach s]
    exact Fintype.sum_equiv e.symm _ _ (by simp)
/-
**Finset.piAntidiag_empty_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {ι : Type u_1} {μ : Type u_2} [inst : DecidableEq ι] [inst_1 : AddCommMo
noid μ] [inst_2 : Finset.HasAntidiagonal μ]   [inst_3 : DecidableEq μ], ∅.piAnti
diag 0 = {0}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma piAntidiag_empty_zero : piAntidiag (∅ : Finset ι) (0 : μ) = {0} := by
  ext; simp [funext_iff]
/-
**Finset.piAntidiag_empty_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {ι : Type u_1} {μ : Type u_2} [inst : DecidableEq ι] [inst_1 : AddCommMo
noid μ] [inst_2 : Finset.HasAntidiagonal μ]   [inst_3 : DecidableEq μ] {n : μ}, 
n ≠ 0 → ∅.piAntidiag n = ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_empty_of_forall_notMem`：eq_empty_of_forall_notMem {s : Finset 
α} (H : forall x, x ∉ s) : s = ∅
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] lemma piAntidiag_empty_of_ne_zero (hn : n ≠ 0) : piAntidiag (∅ : Finset ι) n = ∅ :=
  eq_empty_of_forall_notMem (by simp [hn.symm])
/-
**Finset.piAntidiag_empty** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：piAntidiag_empty (n : μ) : piAntidiag (∅ : Finset ι) n = if n = 0 then {0}
 else ∅
参数：n : μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.piAntidiag_empty_zero`：∀ {ι : Type u_1} {μ : Type u_2} [inst : De
cidableEq ι] [inst_1 : AddCommMonoid μ] [inst_2 : Finset.HasAntidiagonal μ]   [i
nst_3 : DecidableE…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Finset.piAntidiag_empty_of_ne_zero`：∀ {ι : Type u_1} {μ : Type u_2} [ins
t : DecidableEq ι] [inst_1 : AddCommMonoid μ] [inst_2 : Finset.HasAntidiagonal μ
]   [inst_3 : DecidableE…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma piAntidiag_empty (n : μ) : piAntidiag (∅ : Finset ι) n = if n = 0 then {0} else ∅ := by
  split_ifs with hn <;> simp [*]
/-
**Finset.finsetCongr_piAntidiag_eq_antidiag** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：finsetCongr_piAntidiag_eq_antidiag (n : μ) : Equiv.finsetCongr (Equiv.bool
ArrowEquivProd _) (piAntidiag univ n) = antidiagonal n
参数：n : μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Equiv.boolArrowEquivProd_symm_apply`：∀ (α : Type u_9) (p : α × α) (b : B
ool), (Equiv.boolArrowEquivProd α).symm p b = if b = true then p.2 else p.1
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `Bool.true_eq_false`：(true = false) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Bool.false_eq_true`：(false = true) = False
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma finsetCongr_piAntidiag_eq_antidiag (n : μ) :
    Equiv.finsetCongr (Equiv.boolArrowEquivProd _) (piAntidiag univ n) = antidiagonal n := by
  ext ⟨x₁, x₂⟩
  simp_rw [Equiv.finsetCongr_apply, mem_map, Equiv.toEmbedding, Function.Embedding.coeFn_mk,
    ← Equiv.eq_symm_apply]
  simp [add_comm]

end AddCommMonoid

section AddCancelCommMonoid
variable [DecidableEq ι] [AddCancelCommMonoid μ] [HasAntidiagonal μ] [DecidableEq μ] {i : ι}
  {s : Finset ι}

/-
**Finset.pairwiseDisjoint_piAntidiag_map_addRightEmbedding** 是 Mathlib 中的一个引理，位于
命名空间 `Finset`。
形式化陈述：pairwiseDisjoint_piAntidiag_map_addRightEmbedding (hi : i ∉ s) (n : μ) : (
antidiagonal n : Set (μ × μ)).PairwiseDisjoint fun p => map (addRightEmbedding f
un j => if j = i then p.1 else 0) (s.piAntidiag p.2)
参数：hi : i ∉ s；n : μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.instIsRightCancelAdd`：∀ {I : Type u} {f : I → Type v₁} [inst : (i : I
) → Add (f i)] [∀ (i : I), IsRightCancelAdd (f i)],   IsRightCancelAdd ((i : I) 
→ f i)
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.HasAntidiagonal.antidiagonal_congr'`：∀ {A : Type u_1} [inst : Add
CancelCommMonoid A] [inst_1 : Finset.HasAntidiagonal A] {p q : A × A} {n : A},  
 p ∈ Finset.HasAntidiagonal.anti…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `addRightEmbedding.congr_simp`：∀ {G : Type u_1} [inst : Add G] [inst_1 : 
IsRightCancelAdd G] (g g_1 : G),   g = g_1 → addRightEmbedding g = addRightEmbed
ding g_1
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `addRightEmbedding_apply`：∀ {G : Type u_1} [inst : Add G] [inst_1 : IsRig
htCancelAdd G] (g h : G), (addRightEmbedding g) h = h + g
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma pairwiseDisjoint_piAntidiag_map_addRightEmbedding (hi : i ∉ s) (n : μ) :
    (antidiagonal n : Set (μ × μ)).PairwiseDisjoint fun p ↦
      map (addRightEmbedding fun j ↦ if j = i then p.1 else 0) (s.piAntidiag p.2) := by
  rintro ⟨a, b⟩ hab ⟨c, d⟩ hcd
  simp only [ne_eq, HasAntidiagonal.antidiagonal_congr' hab hcd, disjoint_left, mem_map,
    mem_piAntidiag, addRightEmbedding_apply, not_exists, not_and, and_imp, forall_exists_index]
  rintro hfg _ f rfl - rfl g rfl - hgf
  exact hfg <| by simpa [sum_add_distrib, hi] using congr_arg (∑ j ∈ s, · j) hgf.symm
/-
**Finset.piAntidiag_cons** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：piAntidiag_cons (hi : i ∉ s) (n : μ) : piAntidiag (cons i s hi) n = (antid
iagonal n).disjiUnion (fun p : μ × μ => (piAntidiag s p.snd).map (addRightEmbedd
ing fun t => if t = i then p.fst else 0)) (pairwiseDisjoint_piAntidiag_map_addRi
ghtEmbedding hi _)
参数：hi : i ∉ s；n : μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Pi.instIsRightCancelAdd`：∀ {I : Type u} {f : I → Type v₁} [inst : (i : I
) → Add (f i)] [∀ (i : I), IsRightCancelAdd (f i)],   IsRightCancelAdd ((i : I) 
→ f i)
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `Finset.pairwiseDisjoint_piAntidiag_map_addRightEmbedding`：pairwiseDisjoi
nt_piAntidiag_map_addRightEmbedding (hi : i ∉ s) (n : μ) : (antidiagonal n : Set
 (μ × μ)).PairwiseDisjoint fun p => map (addRi…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_cons`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι} 
[inst : AddCommMonoid M] {f : ι → M} (h : a ∉ s),   ∑ x ∈ Finset.cons a s h, f x
 = f …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `addRightEmbedding.congr_simp`：∀ {G : Type u_1} [inst : Add G] [inst_1 : 
IsRightCancelAdd G] (g g_1 : G),   g = g_1 → addRightEmbedding g = addRightEmbed
ding g_1
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Finset.sum_update_of_notMem`：∀ {ι : Type u_1} {M : Type u_3} [inst : Add
CommMonoid M] [inst_1 : DecidableEq ι] {s : Finset ι} {i : ι},   i ∉ s → ∀ (f : 
ι → M) (b : M), ∑…
· 使用定理 `addRightEmbedding_apply`：∀ {G : Type u_1} [inst : Add G] [inst_1 : IsRig
htCancelAdd G] (g h : G), (addRightEmbedding g) h = h + g
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
（共 37 条，此处仅展示前 30 条）
-/
lemma piAntidiag_cons (hi : i ∉ s) (n : μ) :
    piAntidiag (cons i s hi) n = (antidiagonal n).disjiUnion (fun p : μ × μ ↦
      (piAntidiag s p.snd).map (addRightEmbedding fun t ↦ if t = i then p.fst else 0))
        (pairwiseDisjoint_piAntidiag_map_addRightEmbedding hi _) := by
  ext f
  simp only [mem_piAntidiag, sum_cons, ne_eq, mem_cons, mem_disjiUnion, mem_antidiagonal, mem_map,
    Prod.exists]
  constructor
  · rintro ⟨hn, hf⟩
    refine ⟨_, _, hn, update f i 0, ⟨sum_update_of_notMem hi _ _, fun j ↦ ?_⟩, by aesop⟩
    grind
  · rintro ⟨a, _, hn, g, ⟨rfl, hg⟩, rfl⟩
    have := hg i
    aesop (add simp [sum_add_distrib])
/-
**Finset.piAntidiag_insert** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：piAntidiag_insert [DecidableEq (ι -> μ)] (hi : i ∉ s) (n : μ) : piAntidiag
 (insert i s) n = (antidiagonal n).biUnion fun p : μ × μ => (piAntidiag s p.snd)
.image (fun f j => f j + if j = i then p.fst else 0)
参数：ι -> μ；hi : i ∉ s；n : μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.instIsRightCancelAdd`：∀ {I : Type u} {f : I → Type v₁} [inst : (i : I
) → Add (f i)] [∀ (i : I), IsRightCancelAdd (f i)],   IsRightCancelAdd ((i : I) 
→ f i)
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `Finset.pairwiseDisjoint_piAntidiag_map_addRightEmbedding`：pairwiseDisjoi
nt_piAntidiag_map_addRightEmbedding (hi : i ∉ s) (n : μ) : (antidiagonal n : Set
 (μ × μ)).PairwiseDisjoint fun p => map (addRi…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.cons_eq_insert`：cons_eq_insert (a s h) : @cons α a s h = insert a
 s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_left_injective`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd G]
 (a : G), Function.Injective fun x => x + a
· 使用定理 `Finset.map_eq_image`：map_eq_image (f : α ↪ β) (s : Finset α) : s.map f =
 s.image f
· 使用定理 `Finset.disjiUnion.congr_simp`：∀ {α : Type u_1} {β : Type u_2} (s s_1 : F
inset α) (e_s : s = s_1) (t t_1 : α → Finset β) (e_t : t = t_1)   (hf : (↑s).Pai
rwiseDisjoint t), …
· 使用引理 `Finset.disjiUnion_eq_biUnion`：disjiUnion_eq_biUnion (s : Finset α) (f : 
α -> Finset β) (hf) : s.disjiUnion f hf = s.biUnion f
· 使用引理 `Finset.piAntidiag_cons`：piAntidiag_cons (hi : i ∉ s) (n : μ) : piAntidia
g (cons i s hi) n = (antidiagonal n).disjiUnion (fun p : μ × μ => (piAntidiag s 
p.snd).map (…
-/
lemma piAntidiag_insert [DecidableEq (ι → μ)] (hi : i ∉ s) (n : μ) :
    piAntidiag (insert i s) n = (antidiagonal n).biUnion fun p : μ × μ ↦ (piAntidiag s p.snd).image
      (fun f j ↦ f j + if j = i then p.fst else 0) := by
  simpa [map_eq_image, addRightEmbedding] using! piAntidiag_cons hi n

end AddCancelCommMonoid

section CanonicallyOrderedAddCommMonoid
variable [DecidableEq ι] [AddCommMonoid μ] [PartialOrder μ]
  [CanonicallyOrderedAdd μ] [HasAntidiagonal μ] [DecidableEq μ]

/-
**Finset.piAntidiag_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {ι : Type u_1} {μ : Type u_2} [inst : DecidableEq ι] [inst_1 : AddCommMo
noid μ] [inst_2 : PartialOrder μ]   [CanonicallyOrderedAdd μ] [inst_4 : Finset.H
asAntidiagonal μ] [inst_5 : DecidableEq μ] (s : Finset ι),   s.piAntidiag 0 = {0
}
参数：s : Finset ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma piAntidiag_zero (s : Finset ι) : piAntidiag s (0 : μ) = {0} := by
  ext; simp [funext_iff, not_imp_comm, ← forall_and]

end CanonicallyOrderedAddCommMonoid

section Nat
variable [DecidableEq ι]

open Pointwise

/-
**Finset.piAntidiag_univ_fin_eq_antidiagonalTuple** 是 Mathlib 中的一个引理，位于命名空间 `Fin
set`。
形式化陈述：piAntidiag_univ_fin_eq_antidiagonalTuple (n k : Nat) : piAntidiag univ n =
 Nat.antidiagonalTuple k n
参数：n k : Nat。
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
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma piAntidiag_univ_fin_eq_antidiagonalTuple (n k : ℕ) :
    piAntidiag univ n = Nat.antidiagonalTuple k n := by
  ext; simp [Nat.mem_antidiagonalTuple]
/-
**Finset.nsmul_piAntidiag** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：nsmul_piAntidiag [DecidableEq (ι -> Nat)] (s : Finset ι) (m : Nat) {n : Na
t} (hn : n != 0) : n • piAntidiag s m = {f in piAntidiag s (n * m) | forall i in
 s, n ∣ f i}
参数：ι -> Nat；s : Finset ι；m : Nat；hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `Finset.mem_smul_finset`：mem_smul_finset {x : β} : x in a • s ↔ exists y,
 y in s ∧ a • y = x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Nat.instIsDomain`：IsDomain ℕ
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_imp_comm`：not_imp_comm : ¬a -> b ↔ ¬b -> a
· 使用定理 `dvd_zero`：dvd_zero (a : α) : a ∣ 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Nat.mul_div_cancel'`：∀ {n m : ℕ}, n ∣ m → n * (m / n) = m
-/
lemma nsmul_piAntidiag [DecidableEq (ι → ℕ)] (s : Finset ι) (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    n • piAntidiag s m = {f ∈ piAntidiag s (n * m) | ∀ i ∈ s, n ∣ f i} := by
  ext f
  refine mem_smul_finset.trans ?_
  simp only [mem_filter, mem_piAntidiag, and_assoc]
  constructor
  · rintro ⟨f, rfl, hf, rfl⟩
    simpa [← mul_sum, hn] using hf
  rintro ⟨hfsum, hfsup, hfdvd⟩
  have (i : _) : n ∣ f i := by
    by_cases hi : i ∈ s
    · exact hfdvd _ hi
    · rw [not_imp_comm.1 (hfsup _) hi]
      exact dvd_zero _
  refine ⟨fun i ↦ f i / n, ?_⟩
  simp [funext_iff, Nat.mul_div_cancel', ← Nat.sum_div, *]
  grind
/-
**Finset.map_nsmul_piAntidiag** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：map_nsmul_piAntidiag (s : Finset ι) (m : Nat) {n : Nat} (hn : n != 0) : (p
iAntidiag s m).map ⟨(n • ·), nsmul_right_injective hn⟩ = {f in piAntidiag s (n *
 m) | forall i in s, n ∣ f i}
参数：s : Finset ι；m : Nat；hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nsmul_right_injective`：∀ {M : Type u_1} [inst : AddMonoid M] [IsAddTorsi
onFree M] {n : ℕ}, n ≠ 0 → Function.Injective fun a => n • a
· 使用定理 `Pi.instIsAddTorsionFree`：∀ {ι : Type u_1} {M : ι → Type u_3} [inst : (i 
: ι) → AddMonoid (M i)] [∀ (i : ι), IsAddTorsionFree (M i)],   IsAddTorsionFree 
((i : ι) → M …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.map_eq_image`：map_eq_image (f : α ↪ β) (s : Finset α) : s.map f =
 s.image f
· 使用引理 `Finset.nsmul_piAntidiag`：nsmul_piAntidiag [DecidableEq (ι -> Nat)] (s : 
Finset ι) (m : Nat) {n : Nat} (hn : n != 0) : n • piAntidiag s m = {f in piAntid
iag s (n * m)…
-/
lemma map_nsmul_piAntidiag (s : Finset ι) (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    (piAntidiag s m).map ⟨(n • ·), nsmul_right_injective hn⟩ =
        {f ∈ piAntidiag s (n * m) | ∀ i ∈ s, n ∣ f i} := by
  classical rw [map_eq_image]; exact nsmul_piAntidiag _ _ hn
/-
**Finset.nsmul_piAntidiag_univ** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：nsmul_piAntidiag_univ [Fintype ι] (m : Nat) {n : Nat} (hn : n != 0) : n • 
piAntidiag univ m = {f in piAntidiag (univ : Finset ι) (n * m) | forall i, n ∣ f
 i}
参数：m : Nat；hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `Finset.nsmul_piAntidiag`：nsmul_piAntidiag [DecidableEq (ι -> Nat)] (s : 
Finset ι) (m : Nat) {n : Nat} (hn : n != 0) : n • piAntidiag s m = {f in piAntid
iag s (n * m)…
-/
lemma nsmul_piAntidiag_univ [Fintype ι] (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    n • piAntidiag univ m = {f ∈ piAntidiag (univ : Finset ι) (n * m) | ∀ i, n ∣ f i} := by
  simpa using nsmul_piAntidiag (univ : Finset ι) m hn
/-
**Finset.map_nsmul_piAntidiag_univ** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：map_nsmul_piAntidiag_univ [Fintype ι] (m : Nat) {n : Nat} (hn : n != 0) : 
(piAntidiag (univ : Finset ι) m).map ⟨(n • ·), nsmul_right_injective hn⟩ = {f in
 piAntidiag (univ : Finset ι) (n * m) | forall i, n ∣ f i}
参数：m : Nat；hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nsmul_right_injective`：∀ {M : Type u_1} [inst : AddMonoid M] [IsAddTorsi
onFree M] {n : ℕ}, n ≠ 0 → Function.Injective fun a => n • a
· 使用定理 `Pi.instIsAddTorsionFree`：∀ {ι : Type u_1} {M : ι → Type u_3} [inst : (i 
: ι) → AddMonoid (M i)] [∀ (i : ι), IsAddTorsionFree (M i)],   IsAddTorsionFree 
((i : ι) → M …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `Finset.map_nsmul_piAntidiag`：map_nsmul_piAntidiag (s : Finset ι) (m : Na
t) {n : Nat} (hn : n != 0) : (piAntidiag s m).map ⟨(n • ·), nsmul_right_injectiv
e hn⟩ = {f in piA…
-/
lemma map_nsmul_piAntidiag_univ [Fintype ι] (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    (piAntidiag (univ : Finset ι) m).map ⟨(n • ·), nsmul_right_injective hn⟩ =
      {f ∈ piAntidiag (univ : Finset ι) (n * m) | ∀ i, n ∣ f i} := by
  simpa using map_nsmul_piAntidiag (univ : Finset ι) m hn

end Nat

/-
**Finset.map_sym_eq_piAntidiag** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：map_sym_eq_piAntidiag [DecidableEq ι] (s : Finset ι) (n : Nat) : (s.sym n)
.map ⟨fun m a => m.1.count a, Multiset.count_injective.comp Sym.coe_injective⟩ =
 piAntidiag s n
参数：s : Finset ι；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用引理 `Multiset.count_injective`：count_injective : Injective fun (s : Multiset 
α) a => s.count a
· 使用定理 `Sym.coe_injective`：coe_injective : Injective ((↑) : Sym α n -> Multiset 
α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.sum_count_eq_card`：∀ {ι : Type u_1} [inst : DecidableEq ι] {s :
 Finset ι} {m : Multiset ι},   (∀ a ∈ m, a ∈ s) → ∑ a ∈ s, Multiset.count a m = 
m.card
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用引理 `Multiset.card_sum`：card_sum (s : Finset ι) (f : ι -> Multiset α) : card 
(∑ i in s, f i) = ∑ i in s, card (f i)
· 使用引理 `Multiset.card_nsmul`：card_nsmul (s : Multiset α) (n : Nat) : card (n • s
) = n * card s
· 使用定理 `Multiset.card_singleton`：card_singleton (a : α) : card ({a} : Multiset α
) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Multiset.count_sum'`：count_sum' {s : Finset ι} {a : α} {f : ι -> Multise
t α} : count a (∑ x in s, f x) = ∑ x in s, count a (f x)
· 使用引理 `Multiset.count_nsmul`：count_nsmul (a : α) (n s) : count a (n • s) = n * 
count a s
· 使用定理 `Multiset.count_singleton`：count_singleton (a b : α) : count a ({b} : Mul
tiset α) = if a = b then 1 else 0
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
（共 32 条，此处仅展示前 30 条）
-/
lemma map_sym_eq_piAntidiag [DecidableEq ι] (s : Finset ι) (n : ℕ) :
    (s.sym n).map ⟨fun m a ↦ m.1.count a, Multiset.count_injective.comp Sym.coe_injective⟩ =
      piAntidiag s n := by
  ext f
  simp only [Sym.val_eq_coe, mem_map, mem_sym_iff, Embedding.coeFn_mk, funext_iff, Sym.exists,
    Sym.mem_mk, Sym.coe_mk, exists_and_left, exists_prop, mem_piAntidiag, ne_eq]
  constructor
  · rintro ⟨m, hm, rfl, hf⟩
    simpa [← hf, Multiset.sum_count_eq_card hm]
  · rintro ⟨rfl, hf⟩
    refine ⟨∑ a ∈ s, f a • {a}, ?_, ?_⟩
    · simp +contextual
    · simpa [Multiset.count_sum', Multiset.count_singleton, not_imp_comm, eq_comm (a := 0)] using hf

end Finset

