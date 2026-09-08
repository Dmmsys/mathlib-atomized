/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.LinearAlgebra.Alternating.Curry
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Data.Fin.Parity

/-!
# Uncurrying alternating maps

Given a function `f` which is linear in the first argument
and is alternating form in the other `n` arguments,
this file defines an alternating form `AlternatingMap.alternatizeUncurryFin f` in `n + 1` arguments.

This function is given by
```
AlternatingMap.alternatizeUncurryFin f v =
  ∑ i : Fin (n + 1), (-1) ^ (i : ℕ) • f (v i) (removeNth i v)
```

Given an alternating map `f` of `n + 1` arguments,
each term in the sum above written for `f.curryLeft` equals the original map,
thus `f.curryLeft.alternatizeUncurryFin = (n + 1) • f`.

We do not multiply the result of `alternatizeUncurryFin` by `(n + 1)⁻¹`
so that the construction works for `R`-multilinear maps over any commutative ring `R`,
not only a field of characteristic zero.

## Main results

- `AlternatingMap.alternatizeUncurryFin_curryLeft`:
  the round-trip formula for currying/uncurrying, see above.

- `AlternatingMap.alternatizeUncurryFin_alternatizeUncurryFinLM_comp_of_symmetric`:
  If `f` is a symmetric bilinear map taking values in the space of alternating maps,
  then the twice uncurried `f` is zero.

A version of the latter theorem for continuous alternating maps
will be used to prove that the second exterior derivative of a differential form is zero.
-/

@[expose] public section

open Fin Function

namespace AlternatingMap

variable {R : Type*} {M M₂ N N₂ : Type*} [CommRing R] [AddCommGroup M]
  [AddCommGroup M₂] [AddCommGroup N] [AddCommGroup N₂] [Module R M] [Module R M₂]
  [Module R N] [Module R N₂] {n : ℕ}

/-- If `f` is a `(n + 1)`-multilinear alternating map, `x` is an element of the domain,
and `v` is an `n`-vector, then the value of `f` at `v` with `x` inserted at the `p`th place
equals `(-1) ^ p` times the value of `f` at `v` with `x` prepended. -/
/-
**AlternatingMap.map_insertNth** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：map_insertNth (f : M [⋀^Fin (n + 1)]->ₗ[R] N) (p : Fin (n + 1)) (x : M) (v
 : Fin n -> M) : f (p.insertNth x v) = (-1) ^ (p : Nat) • f (Matrix.vecCons x v)
参数：f : M [⋀^Fin (n + 1)]->ₗ[R] N；p : Fin (n + 1)；x : M；v : Fin n -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.cons_comp_cycleRange`：cons_comp_cycleRange {α : Type*} (a : α) (x : 
Fin n -> α) (p : Fin (n + 1)) : (Fin.cons a x : _ -> α) ∘ p.cycleRange = p.inser
tNth a x
· 使用定理 `AlternatingMap.map_perm`：map_perm [DecidableEq ι] [Fintype ι] (v : ι -> 
M) (σ : Equiv.Perm ι) : g (v ∘ σ) = Equiv.Perm.sign σ • g v
· 使用定理 `Matrix.vecCons.eq_1`：∀ {α : Type u} {n : ℕ} (h : α) (t : Fin n → α), Mat
rix.vecCons h t = Fin.cons h t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fin.sign_cycleRange`：sign_cycleRange (i : Fin n) : Perm.sign (cycleRange
 i) = (-1) ^ (i : Nat)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `f` is a `(n + 1)`-multilinear alternating map, `x` is an element of the doma
in,
and `v` is an `n`-vector, then the value of `f` at `v` with `x` inserted at the 
`p`th place
equals `(-1) ^ p` times the value of `f` at `v` with `x` prepended.
-/
theorem map_insertNth (f : M [⋀^Fin (n + 1)]→ₗ[R] N) (p : Fin (n + 1)) (x : M) (v : Fin n → M) :
    f (p.insertNth x v) = (-1) ^ (p : ℕ) • f (Matrix.vecCons x v) := by
  rw [← cons_comp_cycleRange, map_perm, Matrix.vecCons]
  simp [Units.smul_def]
/-
**AlternatingMap.neg_one_pow_smul_map_insertNth** 是 Mathlib 中的一个定理，位于命名空间 `Alter
natingMap`。
形式化陈述：neg_one_pow_smul_map_insertNth (f : M [⋀^Fin (n + 1)]->ₗ[R] N) (p : Fin (n
 + 1)) (x : M) (v : Fin n -> M) : (-1) ^ (p : Nat) • f (p.insertNth x v) = f (Ma
trix.vecCons x v)
参数：f : M [⋀^Fin (n + 1)]->ₗ[R] N；p : Fin (n + 1)；x : M；v : Fin n -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlternatingMap.map_insertNth`：map_insertNth (f : M [⋀^Fin (n + 1)]->ₗ[R]
 N) (p : Fin (n + 1)) (x : M) (v : Fin n -> M) : f (p.insertNth x v) = (-1) ^ (p
 : Nat) • f (Matri…
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用引理 `Even.neg_one_pow`：Even.neg_one_pow (h : Even n) : (-1 : α) ^ n = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem neg_one_pow_smul_map_insertNth (f : M [⋀^Fin (n + 1)]→ₗ[R] N) (p : Fin (n + 1)) (x : M)
    (v : Fin n → M) :
    (-1) ^ (p : ℕ) • f (p.insertNth x v) = f (Matrix.vecCons x v) := by
  rw [map_insertNth, smul_smul, ← pow_add, Even.neg_one_pow, one_smul]
  use p

/-- Let `v` be an `(n + 1)`-tuple with two equal elements `v i = v j`, `i ≠ j`.
Let `w i` (resp., `w j`) be the vector `v` with `i`th (resp., `j`th) element removed.
Then `(-1) ^ i • f (w i) + (-1) ^ j • f (w j) = 0`.
This follows from the fact that these two vectors differ by a permutation of sign `(-1) ^ (i + j)`.

These are the only two nonzero terms in the proof of `map_eq_zero_of_eq`
in the definition of `alternatizeUncurryFin` below. -/
/-
**AlternatingMap.neg_one_pow_smul_map_removeNth_add_eq_zero_of_eq** 是 Mathlib 中的
一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：neg_one_pow_smul_map_removeNth_add_eq_zero_of_eq (f : M [⋀^Fin n]->ₗ[R] N)
 {v : Fin (n + 1) -> M} {i j : Fin (n + 1)} (hvij : v i = v j) (hij : i != j) : 
(-1) ^ (i : Nat) • f (i.removeNth v) + (-1) ^ (j : Nat) • f (j.removeNth v) = 0
参数：f : M [⋀^Fin n]->ₗ[R] N；n + 1；n + 1；hvij : v i = v j；hij : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Fin.exists_succAbove_eq`：exists_succAbove_eq {x y : Fin (n + 1)} (h : x 
!= y) : exists z, y.succAbove z = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Fin.pos`：∀ {n : ℕ} (i : Fin n), 0 < n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Fin.insertNth_self_removeNth`：insertNth_self_removeNth (p : Fin (n + 1))
 (f : forall j, α j) : insertNth p (f p) (removeNth p f) = f
· 使用定理 `Fin.removeNth_removeNth_eq_swap`：removeNth_removeNth_eq_swap {α : Sort*}
 (m : Fin (n + 2) -> α) (i : Fin (n + 1)) (j : Fin (n + 2)) : i.removeNth (j.rem
oveNth m) = (i.predAb…
· 使用定理 `Fin.removeNth.eq_1`：∀ {n : ℕ} {α : Fin (n + 1) → Sort u_1} (p : Fin (n +
 1)) (f : (i : Fin (n + 1)) → α i) (i : Fin n),   p.removeNth f i = f (p.succAbo
ve i)
· 使用定理 `Fin.succAbove_succAbove_predAbove`：succAbove_succAbove_predAbove {n : Na
t} (i : Fin (n + 1)) (j : Fin n) : (i.succAbove j).succAbove (j.predAbove i) = i
· 使用定理 `AlternatingMap.map_insertNth`：map_insertNth (f : M [⋀^Fin (n + 1)]->ₗ[R]
 N) (p : Fin (n + 1)) (x : M) (v : Fin n -> M) : f (p.insertNth x v) = (-1) ^ (p
 : Nat) • f (Matri…
· 使用定理 `AlternatingMap.neg_one_pow_smul_map_insertNth`：neg_one_pow_smul_map_inse
rtNth (f : M [⋀^Fin (n + 1)]->ₗ[R] N) (p : Fin (n + 1)) (x : M) (v : Fin n -> M)
 : (-1) ^ (p : Nat) • f (p.insertNt…
· 使用定理 `Fin.insertNth_removeNth`：∀ {n : ℕ} {α : Fin (n + 1) → Sort u_1} (p : Fin
 (n + 1)) (x : α p) (f : (j : Fin (n + 1)) → α j),   p.insertNth x (p.removeNth 
f) = Function…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.update_eq_self_iff`：∀ {α : Sort u} {β : α → Sort v} [inst : Dec
idableEq α] {f : (a : α) → β a} {a : α} {b : β a},   Function.update f a b = f ↔
 b = f a
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用引理 `Fin.neg_one_pow_succAbove_add_predAbove`：neg_one_pow_succAbove_add_predA
bove {R : Type*} [Monoid R] [HasDistribNeg R] (i : Fin (n + 1)) (j : Fin n) : (-
1 : R) ^ (i.succAbove j + j.p…
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用引理 `pow_mul'`：pow_mul' (a : M) (m n : Nat) : a ^ (m * n) = (a ^ n) ^ m
· 使用定理 `neg_one_pow_two`：∀ {R : Type u} [inst : Monoid R] [inst_1 : HasDistribNe
g R], (-1) ^ 2 = 1
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0

--- 原说明 ---
Let `v` be an `(n + 1)`-tuple with two equal elements `v i = v j`, `i ≠ j`.
Let `w i` (resp., `w j`) be the vector `v` with `i`th (resp., `j`th) element rem
oved.
Then `(-1) ^ i • f (w i) + (-1) ^ j • f (w j) = 0`.
This follows from the fact that these two vectors differ by a permutation of sig
n `(-1) ^ (i + j)`.

These are the only two nonzero terms in the proof of `map_eq_zero_of_eq`
in the definition of `alternatizeUncurryFin` below.
-/
theorem neg_one_pow_smul_map_removeNth_add_eq_zero_of_eq (f : M [⋀^Fin n]→ₗ[R] N)
    {v : Fin (n + 1) → M} {i j : Fin (n + 1)} (hvij : v i = v j) (hij : i ≠ j) :
    (-1) ^ (i : ℕ) • f (i.removeNth v) + (-1) ^ (j : ℕ) • f (j.removeNth v) = 0 := by
  rcases exists_succAbove_eq hij with ⟨i, rfl⟩
  obtain ⟨m, rfl⟩ : ∃ m, m + 1 = n := by simp [i.pos]
  rw [← (i.predAbove j).insertNth_self_removeNth (removeNth _ _), ← removeNth_removeNth_eq_swap,
    removeNth, succAbove_succAbove_predAbove, map_insertNth, ← neg_one_pow_smul_map_insertNth,
    insertNth_removeNth, update_eq_self_iff.2, smul_smul, ← pow_add,
    neg_one_pow_succAbove_add_predAbove, neg_smul, pow_add, mul_smul,
    smul_smul (_ ^ i.val), ← sq, ← pow_mul, pow_mul', neg_one_pow_two, one_pow, one_smul,
    neg_add_cancel]
  exact hvij.symm

/-- Given a function which is linear in the first argument
and is alternating in the other `n` arguments,
build an alternating form in `n + 1` arguments.

The function is given by
```
alternatizeUncurryFin f v = ∑ i : Fin (n + 1), (-1) ^ (i : ℕ) • f (v i) (removeNth i v)
```

Note that the round-trip with `curryFin` multiplies the form by `n + 1`,
since we want to avoid division in this definition. -/
/-
**AlternatingMap.alternatizeUncurryFin** 是 Mathlib 中的一个定义，位于命名空间 `AlternatingMap
`。
形式化陈述：alternatizeUncurryFin (f : M ->ₗ[R] M [⋀^Fin n]->ₗ[R] N) : M [⋀^Fin (n + 1
)]->ₗ[R] N where toMultilinearMap
参数：f : M ->ₗ[R] M [⋀^Fin n]->ₗ[R] N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a function which is linear in the first argument
and is alternating in the other `n` arguments,
build an alternating form in `n + 1` arguments.

The function is given by
```
alternatizeUncurryFin f v = ∑ i : Fin (n + 1), (-1) ^ (i : ℕ) • f (v i) (removeN
th i v)
```

Note that the round-trip with `curryFin` multiplies the form by `n + 1`,
since we want to avoid division in this definition.
-/
def alternatizeUncurryFin (f : M →ₗ[R] M [⋀^Fin n]→ₗ[R] N) :
    M [⋀^Fin (n + 1)]→ₗ[R] N where
  toMultilinearMap :=
    ∑ p : Fin (n + 1), (-1) ^ (p : ℕ) • LinearMap.uncurryMid p (toMultilinearMapLM ∘ₗ f)
  map_eq_zero_of_eq' := by
    intro v i j hvij hij
    suffices ∑ k : Fin (n + 1), (-1) ^ (k : ℕ) • f (v k) (k.removeNth v) = 0 by simpa
    calc
      _ = (-1) ^ (i : ℕ) • f (v i) (i.removeNth v) + (-1) ^ (j : ℕ) • f (v j) (j.removeNth v) := by
        refine Fintype.sum_eq_add _ _ hij fun k ⟨hki, hkj⟩ ↦ ?_
        rcases exists_succAbove_eq hki.symm with ⟨i, rfl⟩
        rcases exists_succAbove_eq hkj.symm with ⟨j, rfl⟩
        rw [(f (v k)).map_eq_zero_of_eq _ hvij (ne_of_apply_ne _ hij), smul_zero]
      _ = 0 := by
        rw [hvij, neg_one_pow_smul_map_removeNth_add_eq_zero_of_eq] <;> assumption
/-
**AlternatingMap.alternatizeUncurryFin_apply** 是 Mathlib 中的一个定理，位于命名空间 `Alternat
ingMap`。
形式化陈述：alternatizeUncurryFin_apply (f : M ->ₗ[R] M [⋀^Fin n]->ₗ[R] N) (v : Fin (n
 + 1) -> M) : alternatizeUncurryFin f v = ∑ i : Fin (n + 1), (-1) ^ (i : Nat) • 
f (v i) (removeNth i v)
参数：f : M ->ₗ[R] M [⋀^Fin n]->ₗ[R] N；v : Fin (n + 1) -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `AlternatingMap.mk.congr_simp`：∀ {R : Type u_1} [inst : Semiring R] {M : 
Type u_2} [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {N : Type u_
3} [inst_3 : AddCo…
· 使用定理 `sum_apply`：∀ {F : Type u_8} {α : Type u_9} {β : Type u_10} {ι : Type u_1
1} [inst : FunLike F α β] [inst_1 : AddCommMonoid β]   [inst_2 : AddCommMonoid …
· 使用定理 `MultilinearMap.instIsZeroApplyForall`：∀ {R : Type uR} {ι : Type uι} {M₁ 
: ι → Type v₁} {M₂ : Type v₂} [inst : Semiring R]   [inst_1 : (i : ι) → AddCommM
onoid (M₁ i)] [inst_2 : Ad…
· 使用定理 `MultilinearMap.instIsAddApplyForall`：∀ {R : Type uR} {ι : Type uι} {M₁ :
 ι → Type v₁} {M₂ : Type v₂} [inst : Semiring R]   [inst_1 : (i : ι) → AddCommMo
noid (M₁ i)] [inst_2 : Ad…
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `MultilinearMap.instIsSMulApplyForall`：∀ {R : Type uR} {S : Type uS} {ι :
 Type uι} {M₁ : ι → Type v₁} {M₂ : Type v₂} [inst : Semiring R]   [inst_1 : (i :
 ι) → AddCommMonoid (M₁ i)…
· 使用定理 `LinearMap.uncurryMid_apply`：∀ {R : Type uR} {n : ℕ} {M : Fin n.succ → Ty
pe v} {M₂ : Type v₂} [inst : CommSemiring R]   [inst_1 : (i : Fin n.succ) → AddC
ommMonoid (M i)]…
· 使用定理 `AlternatingMap.toMultilinearMapLM_apply`：∀ {R : Type u_1} [inst : Semiri
ng R] {M : Type u_2} [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {
N : Type u_3} [inst_3 : AddCo…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem alternatizeUncurryFin_apply (f : M →ₗ[R] M [⋀^Fin n]→ₗ[R] N) (v : Fin (n + 1) → M) :
    alternatizeUncurryFin f v = ∑ i : Fin (n + 1), (-1) ^ (i : ℕ) • f (v i) (removeNth i v) := by
  simp [alternatizeUncurryFin]

@[simp]
/-
**AlternatingMap.alternatizeUncurryFin_add** 是 Mathlib 中的一个定理，位于命名空间 `Alternatin
gMap`。
形式化陈述：alternatizeUncurryFin_add (f g : M ->ₗ[R] M [⋀^Fin n]->ₗ[R] N) : alternati
zeUncurryFin (f + g) = alternatizeUncurryFin f + alternatizeUncurryFin g
参数：f g : M ->ₗ[R] M [⋀^Fin n]->ₗ[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlternatingMap.ext`：ext {f f' : M [⋀^ι]->ₗ[R] N} (H : forall x, f x = f'
 x) : f = f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlternatingMap.alternatizeUncurryFin_apply`：alternatizeUncurryFin_apply 
(f : M ->ₗ[R] M [⋀^Fin n]->ₗ[R] N) (v : Fin (n + 1) -> M) : alternatizeUncurryFi
n f v = ∑ i : Fin (n + 1), (-1) …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem alternatizeUncurryFin_add (f g : M →ₗ[R] M [⋀^Fin n]→ₗ[R] N) :
    alternatizeUncurryFin (f + g) = alternatizeUncurryFin f + alternatizeUncurryFin g := by
  ext
  simp [alternatizeUncurryFin_apply, Finset.sum_add_distrib]

@[simp]
/-
**AlternatingMap.alternatizeUncurryFin_curryLeft** 是 Mathlib 中的一个引理，位于命名空间 `Alte
rnatingMap`。
形式化陈述：alternatizeUncurryFin_curryLeft (f : M [⋀^Fin (n + 1)]->ₗ[R] N) : alternat
izeUncurryFin (curryLeft f) = (n + 1) • f
参数：f : M [⋀^Fin (n + 1)]->ₗ[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlternatingMap.ext`：ext {f f' : M [⋀^ι]->ₗ[R] N} (H : forall x, f x = f'
 x) : f = f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlternatingMap.alternatizeUncurryFin_apply`：alternatizeUncurryFin_apply 
(f : M ->ₗ[R] M [⋀^Fin n]->ₗ[R] N) (v : Fin (n + 1) -> M) : alternatizeUncurryFi
n f v = ∑ i : Fin (n + 1), (-1) …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fin.insertNth_removeNth`：∀ {n : ℕ} {α : Fin (n + 1) → Sort u_1} (p : Fin
 (n + 1)) (x : α p) (f : (j : Fin (n + 1)) → α j),   p.insertNth x (p.removeNth 
f) = Function…
· 使用定理 `Function.update_eq_self`：update_eq_self (a : α) (f : forall a, β a) : up
date f a (f a) = f
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma alternatizeUncurryFin_curryLeft (f : M [⋀^Fin (n + 1)]→ₗ[R] N) :
    alternatizeUncurryFin (curryLeft f) = (n + 1) • f := by
  ext v
  simp [alternatizeUncurryFin_apply, ← map_insertNth]

variable {S : Type*} [Monoid S] [DistribMulAction S N] [SMulCommClass R S N]

@[simp]
/-
**AlternatingMap.alternatizeUncurryFin_smul** 是 Mathlib 中的一个定理，位于命名空间 `Alternati
ngMap`。
形式化陈述：alternatizeUncurryFin_smul (c : S) (f : M ->ₗ[R] M [⋀^Fin n]->ₗ[R] N) : al
ternatizeUncurryFin (c • f) = c • alternatizeUncurryFin f
参数：c : S；f : M ->ₗ[R] M [⋀^Fin n]->ₗ[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlternatingMap.ext`：ext {f f' : M [⋀^ι]->ₗ[R] N} (H : forall x, f x = f'
 x) : f = f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlternatingMap.alternatizeUncurryFin_apply`：alternatizeUncurryFin_apply 
(f : M ->ₗ[R] M [⋀^Fin n]->ₗ[R] N) (v : Fin (n + 1) -> M) : alternatizeUncurryFi
n f v = ∑ i : Fin (n + 1), (-1) …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem alternatizeUncurryFin_smul (c : S) (f : M →ₗ[R] M [⋀^Fin n]→ₗ[R] N) :
    alternatizeUncurryFin (c • f) = c • alternatizeUncurryFin f := by
  ext v
  simp [alternatizeUncurryFin_apply, smul_comm _ c, Finset.smul_sum]

/-- `AlternatingMap.alternatizeUncurryFin` as a linear map. -/
@[simps! apply]
/-
**AlternatingMap.alternatizeUncurryFinLM** 是 Mathlib 中的一个定义，位于命名空间 `AlternatingM
ap`。
形式化陈述：alternatizeUncurryFinLM : (M ->ₗ[R] M [⋀^Fin n]->ₗ[R] N) ->ₗ[R] M [⋀^Fin (
n + 1)]->ₗ[R] N where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlternatingMap.alternatizeUncurryFin_add`：alternatizeUncurryFin_add (f g
 : M ->ₗ[R] M [⋀^Fin n]->ₗ[R] N) : alternatizeUncurryFin (f + g) = alternatizeUn
curryFin f + alternatizeUncurr…

--- 原说明 ---
`AlternatingMap.alternatizeUncurryFin` as a linear map.
-/
def alternatizeUncurryFinLM : (M →ₗ[R] M [⋀^Fin n]→ₗ[R] N) →ₗ[R] M [⋀^Fin (n + 1)]→ₗ[R] N where
  toFun := alternatizeUncurryFin
  map_add' := alternatizeUncurryFin_add
  map_smul' := alternatizeUncurryFin_smul

/-- If `f` is a bilinear map taking values in the space of alternating maps,
then evaluation of the twice uncurried `f` on a tuple of vectors `v`
can be represented as a sum of

$$
f(v_i, v_j; v_0, \dots, \hat{v_i}, \dots, \hat{v_j}-) -
f(v_j, v_i; v_0, \dots, \hat{v_i}, \dots, \hat{v_j}-)
$$

over all `(i j : Fin (n + 2))`, `i < j`, taken with appropriate signs.
Here $\hat{v_i}$ and $\hat{v_j}$ mean that these vectors are removed from the tuple.

We use pairs of `i j : Fin (n + 1)`, `i ≤ j`,
to encode pairs `(i.castSucc : Fin (n + 2), j.succ : Fin (n + 2))`,
so the power of `-1` is off by one compared to the informal texts.

In particular, if `f` is symmetric in the first two arguments,
then the resulting alternating map is zero,
see `alternatizeUncurryFin_alternatizeUncurryFinLM_comp_of_symmetric` below.
-/
/-
**AlternatingMap.alternatizeUncurryFin_alternatizeUncurryFinLM_comp_apply** 是 Ma
thlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：alternatizeUncurryFin_alternatizeUncurryFinLM_comp_apply (f : M ->ₗ[R] M -
>ₗ[R] M [⋀^Fin n]->ₗ[R] N) (v : Fin (n + 2) -> M) : alternatizeUncurryFin (alter
natizeUncurryFinLM ∘ₗ f) v = ∑ (i : Fin (n + 1)), ∑ j >= i, (-1 : Int) ^ (i + j 
: Nat) • (f (v i.castSucc) (v j.succ) (j.removeNth <| i.castSucc.removeNth v) - 
f (v j.succ) (v i.castSucc) (j.removeNth <| i.castSucc.removeNth v))
参数：f : M ->ₗ[R] M ->ₗ[R] M [⋀^Fin n]->ₗ[R] N；v : Fin (n + 2) -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlternatingMap.alternatizeUncurryFin_apply`：alternatizeUncurryFin_apply 
(f : M ->ₗ[R] M [⋀^Fin n]->ₗ[R] N) (v : Fin (n + 1) -> M) : alternatizeUncurryFi
n f v = ∑ i : Fin (n + 1), (-1) …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `AlternatingMap.alternatizeUncurryFinLM_apply`：∀ {R : Type u_1} {M : Type
 u_2} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : Add
CommGroup N]   [inst_3 : _root_.Mo…
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
· 使用定理 `Fin.sum_sum_eq_sum_triangle_add`：∀ {M : Type u_2} [inst : AddCommMonoid 
M] {n : ℕ} (f : Fin (n + 1) → Fin n → M),   ∑ i, ∑ j, f i j = ∑ i, ∑ j ≥ i, (f i
.castSucc j + f j.suc…
· 使用定理 `Fintype.sum_congr`：∀ {α : Type u_1} {M : Type u_4} [inst : Fintype α] [i
nst_1 : AddCommMonoid M] (f g : α → M),   (∀ (a : α), f a = g a) → ∑ a, f a = ∑ 
a, g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `Fin.succAbove_of_le_castSucc`：succAbove_of_le_castSucc (p : Fin (n + 1))
 (i : Fin n) (h : p <= castSucc i) : p.succAbove i = i.succ
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Finset.mem_Ici`：mem_Ici : x in Ici a ↔ a <= x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Fin.succAbove_of_castSucc_lt`：succAbove_of_castSucc_lt (p : Fin (n + 1))
 (i : Fin n) (h : castSucc i < p) : p.succAbove i = castSucc i
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `neg_one_smul`：neg_one_smul (x : M) : (-1 : R) • x = -x
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Fin.removeNth_removeNth_eq_swap`：removeNth_removeNth_eq_swap {α : Sort*}
 (m : Fin (n + 2) -> α) (i : Fin (n + 1)) (j : Fin (n + 2)) : i.removeNth (j.rem
oveNth m) = (i.predAb…
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Fin.pred_succ`：∀ {n : ℕ} (i : Fin n) {h : i.succ ≠ 0}, i.succ.pred h = i
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a

--- 原说明 ---
If `f` is a bilinear map taking values in the space of alternating maps,
then evaluation of the twice uncurried `f` on a tuple of vectors `v`
can be represented as a sum of

$$
f(v_i, v_j; v_0, \dots, \hat{v_i}, \dots, \hat{v_j}-) -
f(v_j, v_i; v_0, \dots, \hat{v_i}, \dots, \hat{v_j}-)
$$

over all `(i j : Fin (n + 2))`, `i < j`, taken with appropriate signs.
Here $\hat{v_i}$ and $\hat{v_j}$ mean that these vectors are removed from the tu
ple.

We use pairs of `i j : Fin (n + 1)`, `i ≤ j`,
to encode pairs `(i.castSucc : Fin (n + 2), j.succ : Fin (n + 2))`,
so the power of `-1` is off by one compared to the informal texts.

In particular, if `f` is symmetric in the first two arguments,
then the resulting alternating map is zero,
see `alternatizeUncurryFin_alternatizeUncurryFinLM_comp_of_symmetric` below.
-/
theorem alternatizeUncurryFin_alternatizeUncurryFinLM_comp_apply
    (f : M →ₗ[R] M →ₗ[R] M [⋀^Fin n]→ₗ[R] N) (v : Fin (n + 2) → M) :
    alternatizeUncurryFin (alternatizeUncurryFinLM ∘ₗ f) v =
      ∑ (i : Fin (n + 1)), ∑ j ≥ i,
        (-1 : ℤ) ^ (i + j : ℕ) •
          (f (v i.castSucc) (v j.succ) (j.removeNth <| i.castSucc.removeNth v) -
            f (v j.succ) (v i.castSucc) (j.removeNth <| i.castSucc.removeNth v)) := by
  simp only [alternatizeUncurryFin_apply, Int.reduceNeg, LinearMap.coe_comp, comp_apply,
    alternatizeUncurryFinLM_apply, Finset.smul_sum, sum_sum_eq_sum_triangle_add, val_castSucc,
    val_succ]
  refine Fintype.sum_congr _ _ fun i ↦ Finset.sum_congr rfl fun j hj ↦ ?_
  rw [Finset.mem_Ici] at hj
  have H₁ : i.castSucc.removeNth v j = v j.succ := by
    simp [Fin.removeNth_apply, Fin.succAbove_of_le_castSucc, hj]
  have H₂ : j.succ.removeNth v i = v i.castSucc := by
    simp [Fin.removeNth_apply, Fin.succAbove_of_castSucc_lt, hj]
  simp only [pow_add, mul_smul, pow_one, neg_one_smul, smul_neg, smul_sub, ← sub_eq_add_neg,
    smul_comm ((-1 : ℤ) ^ (j : ℕ)), H₁, H₂]
  congr 4
  rw [removeNth_removeNth_eq_swap]
  simp [Fin.predAbove, hj, Fin.succAbove]

/-- If `f` is a symmetric bilinear map taking values in the space of alternating maps,
then the twice uncurried `f` is zero.

See also `alternatizeUncurryFin_alternatizeUncurryFinLM_comp_apply`
for a formula that does not assume `f` to be symmetric. -/
/-
**AlternatingMap.alternatizeUncurryFin_alternatizeUncurryFinLM_comp_of_symmetric
** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：alternatizeUncurryFin_alternatizeUncurryFinLM_comp_of_symmetric {f : M ->ₗ
[R] M ->ₗ[R] M [⋀^Fin n]->ₗ[R] N} (hf : forall x y, f x y = f y x) : alternatize
UncurryFin (alternatizeUncurryFinLM ∘ₗ f) = 0
参数：hf : forall x y, f x y = f y x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlternatingMap.ext`：ext {f f' : M [⋀^ι]->ₗ[R] N} (H : forall x, f x = f'
 x) : f = f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlternatingMap.alternatizeUncurryFin_alternatizeUncurryFinLM_comp_apply`
：alternatizeUncurryFin_alternatizeUncurryFinLM_comp_apply (f : M ->ₗ[R] M ->ₗ[R]
 M [⋀^Fin n]->ₗ[R] N) (v : Fin (n + 2) -> M) : alternatizeUnc…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `f` is a symmetric bilinear map taking values in the space of alternating map
s,
then the twice uncurried `f` is zero.

See also `alternatizeUncurryFin_alternatizeUncurryFinLM_comp_apply`
for a formula that does not assume `f` to be symmetric.
-/
theorem alternatizeUncurryFin_alternatizeUncurryFinLM_comp_of_symmetric
    {f : M →ₗ[R] M →ₗ[R] M [⋀^Fin n]→ₗ[R] N} (hf : ∀ x y, f x y = f y x) :
    alternatizeUncurryFin (alternatizeUncurryFinLM ∘ₗ f) = 0 := by
  ext v
  simp [alternatizeUncurryFin_alternatizeUncurryFinLM_comp_apply, hf (v <| .castSucc _)]

end AlternatingMap

