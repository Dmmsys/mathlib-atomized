/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.Algebra.Module.Submodule.Ker

/-!

# Iterate maps and comaps of submodules

Some preliminary work for establishing the strong rank condition for Noetherian rings.

Given two linear maps `f i : N →ₗ[R] M` and a submodule `K : Submodule R N`, we can define
`LinearMap.iterateMapComap f i n K : Submodule R N` to be `f⁻¹(i(⋯(f⁻¹(i(K)))))` (`n` times).
If `f(K) ≤ i(K)`, then this sequence is non-decreasing (`LinearMap.iterateMapComap_le_succ`).
On the other hand, if `f` is surjective, `i` is injective, and there exists some `m` such that
`LinearMap.iterateMapComap f i m K = LinearMap.iterateMapComap f i (m + 1) K`,
then for any `n`,
`LinearMap.iterateMapComap f i n K = LinearMap.iterateMapComap f i (n + 1) K`.
In particular, by taking `n = 0`, the kernel of `f` is contained in `K`
(`LinearMap.ker_le_of_iterateMapComap_eq_succ`),
which is a consequence of `LinearMap.ker_le_comap`.
As a special case, if one can take `K` to be zero,
then `f` is injective. This is the key result for establishing the strong rank condition
for Noetherian rings.

The construction here is adapted from the proof in Djoković's paper
*Epimorphisms of modules which must be isomorphisms* [djokovic1973].

-/

@[expose] public section

open Function Submodule

namespace LinearMap

variable {R N M : Type*} [Semiring R] [AddCommMonoid N] [Module R N]
  [AddCommMonoid M] [Module R M] (f i : N →ₗ[R] M)

/-- The `LinearMap.iterateMapComap f i n K : Submodule R N` is
`f⁻¹(i(⋯(f⁻¹(i(K)))))` (`n` times). -/
/-
**LinearMap.iterateMapComap** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：iterateMapComap (n : Nat)
参数：n : Nat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `LinearMap.iterateMapComap f i n K : Submodule R N` is
`f⁻¹(i(⋯(f⁻¹(i(K)))))` (`n` times).
-/
def iterateMapComap (n : ℕ) := (fun K : Submodule R N ↦ (K.map i).comap f)^[n]

/-- If `f(K) ≤ i(K)`, then `LinearMap.iterateMapComap` is not decreasing. -/
/-
**LinearMap.iterateMapComap_le_succ** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：iterateMapComap_le_succ (K : Submodule R N) (h : K.map f <= K.map i) (n : 
Nat) : f.iterateMapComap i n K <= f.iterateMapComap i (n + 1) K
参数：K : Submodule R N；h : K.map f <= K.map i；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.iterateMapComap.eq_1`：∀ {R : Type u_1} {N : Type u_2} {M : Typ
e u_3} [inst : Semiring R] [inst_1 : AddCommMonoid N]   [inst_2 : _root_.Module 
R N] [inst_3 : AddCo…
· 使用定理 `Function.iterate_succ'`：iterate_succ' (n : Nat) : f^[n.succ] = f ∘ f^[n]
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.map_le_iff_le_comap`：map_le_iff_le_comap {f : M ->ₛₗ[σ₁₂] M₂} 
{p : Submodule R M} {q : Submodule R₂ M₂} : map f p <= q ↔ p <= comap f q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Submodule.map.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Submodule.map_comap_le`：map_comap_le [RingHomSurjective σ₁₂] (f : M ->ₛₗ
[σ₁₂] M₂) (q : Submodule R₂ M₂) : map f (comap f q) <= q
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Submodule.map_mono`：map_mono {f : M ->ₛₗ[σ₁₂] M₂} {p p' : Submodule R M}
 : p <= p' -> map f p <= map f p'
· 使用定理 `Submodule.le_comap_map`：le_comap_map [RingHomSurjective σ₁₂] (f : M ->ₛₗ
[σ₁₂] M₂) (p : Submodule R M) : p <= comap f (map f p)
· 使用定理 `Submodule.comap_mono`：comap_mono {f : M ->ₛₗ[σ₁₂] M₂} {q q' : Submodule 
R₂ M₂} : q <= q' -> comap f q <= comap f q'

--- 原说明 ---
If `f(K) ≤ i(K)`, then `LinearMap.iterateMapComap` is not decreasing.
-/
theorem iterateMapComap_le_succ (K : Submodule R N) (h : K.map f ≤ K.map i) (n : ℕ) :
    f.iterateMapComap i n K ≤ f.iterateMapComap i (n + 1) K := by
  nth_rw 2 [iterateMapComap]
  rw [iterate_succ', Function.comp_apply, ← iterateMapComap, ← map_le_iff_le_comap]
  induction n with
  | zero => exact h
  | succ n ih =>
    simp_rw [iterateMapComap, iterate_succ', Function.comp_apply]
    calc
      _ ≤ (f.iterateMapComap i n K).map i := map_comap_le _ _
      _ ≤ (((f.iterateMapComap i n K).map f).comap f).map i := by grw [← le_comap_map]
      _ ≤ _ := by gcongr; exact ih

/-- If `f` is surjective, `i` is injective, and there exists some `m` such that
`LinearMap.iterateMapComap f i m K = LinearMap.iterateMapComap f i (m + 1) K`,
then for any `n`,
`LinearMap.iterateMapComap f i n K = LinearMap.iterateMapComap f i (n + 1) K`.
In particular, by taking `n = 0`, the kernel of `f` is contained in `K`
(`LinearMap.ker_le_of_iterateMapComap_eq_succ`),
which is a consequence of `LinearMap.ker_le_comap`. -/
/-
**LinearMap.iterateMapComap_eq_succ** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：iterateMapComap_eq_succ (K : Submodule R N) (m : Nat) (heq : f.iterateMapC
omap i m K = f.iterateMapComap i (m + 1) K) (hf : Surjective f) (hi : Injective 
i) (n : Nat) : f.iterateMapComap i n K = f.iterateMapComap i (n + 1) K
参数：K : Submodule R N；m : Nat；heq : f.iterateMapComap i m K = f.iterateMapComap i
 (m + 1) K；hf : Surjective f；hi : Injective i；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.iterateMapComap.eq_1`：∀ {R : Type u_1} {N : Type u_2} {M : Typ
e u_3} [inst : Semiring R] [inst_1 : AddCommMonoid N]   [inst_2 : _root_.Module 
R N] [inst_3 : AddCo…
· 使用定理 `Function.iterate_succ'`：iterate_succ' (n : Nat) : f^[n.succ] = f ∘ f^[n]
· 使用定理 `Submodule.map_injective_of_injective`：map_injective_of_injective : Funct
ion.Injective (map f)
· 使用定理 `Submodule.comap_injective_of_surjective`：comap_injective_of_surjective :
 Function.Injective (comap f)
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If `f` is surjective, `i` is injective, and there exists some `m` such that
`LinearMap.iterateMapComap f i m K = LinearMap.iterateMapComap f i (m + 1) K`,
then for any `n`,
`LinearMap.iterateMapComap f i n K = LinearMap.iterateMapComap f i (n + 1) K`.
In particular, by taking `n = 0`, the kernel of `f` is contained in `K`
(`LinearMap.ker_le_of_iterateMapComap_eq_succ`),
which is a consequence of `LinearMap.ker_le_comap`.
-/
theorem iterateMapComap_eq_succ (K : Submodule R N)
    (m : ℕ) (heq : f.iterateMapComap i m K = f.iterateMapComap i (m + 1) K)
    (hf : Surjective f) (hi : Injective i) (n : ℕ) :
    f.iterateMapComap i n K = f.iterateMapComap i (n + 1) K := by
  induction n with
  | zero =>
    contrapose! heq
    induction m with
    | zero => exact heq
    | succ m ih =>
      rw [iterateMapComap, iterateMapComap, iterate_succ', iterate_succ']
      exact fun H ↦ ih (map_injective_of_injective hi (comap_injective_of_surjective hf H))
  | succ n ih =>
    rw [iterateMapComap, iterateMapComap, iterate_succ', iterate_succ',
      Function.comp_apply, Function.comp_apply, ← iterateMapComap, ← iterateMapComap, ih]

/-- If `f` is surjective, `i` is injective, and there exists some `m` such that
`LinearMap.iterateMapComap f i m K = LinearMap.iterateMapComap f i (m + 1) K`,
then the kernel of `f` is contained in `K`.
This is a corollary of `LinearMap.iterateMapComap_eq_succ` and `LinearMap.ker_le_comap`.
As a special case, if one can take `K` to be zero,
then `f` is injective. This is the key result for establishing the strong rank condition
for Noetherian rings. -/
/-
**LinearMap.ker_le_of_iterateMapComap_eq_succ** 是 Mathlib 中的一个定理，位于命名空间 `LinearM
ap`。
形式化陈述：ker_le_of_iterateMapComap_eq_succ (K : Submodule R N) (m : Nat) (heq : f.i
terateMapComap i m K = f.iterateMapComap i (m + 1) K) (hf : Surjective f) (hi : 
Injective i) : LinearMap.ker f <= K
参数：K : Submodule R N；m : Nat；heq : f.iterateMapComap i m K = f.iterateMapComap i
 (m + 1) K；hf : Surjective f；hi : Injective i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.iterateMapComap_eq_succ`：iterateMapComap_eq_succ (K : Submodul
e R N) (m : Nat) (heq : f.iterateMapComap i m K = f.iterateMapComap i (m + 1) K)
 (hf : Surjective f) (h…
· 使用定理 `LinearMap.ker_le_comap`：ker_le_comap {p : Submodule R₂ M₂} (f : M ->ₛₗ[τ
₁₂] M₂) : ker f <= p.comap f

--- 原说明 ---
If `f` is surjective, `i` is injective, and there exists some `m` such that
`LinearMap.iterateMapComap f i m K = LinearMap.iterateMapComap f i (m + 1) K`,
then the kernel of `f` is contained in `K`.
This is a corollary of `LinearMap.iterateMapComap_eq_succ` and `LinearMap.ker_le
_comap`.
As a special case, if one can take `K` to be zero,
then `f` is injective. This is the key result for establishing the strong rank c
ondition
for Noetherian rings.
-/
theorem ker_le_of_iterateMapComap_eq_succ (K : Submodule R N)
    (m : ℕ) (heq : f.iterateMapComap i m K = f.iterateMapComap i (m + 1) K)
    (hf : Surjective f) (hi : Injective i) : LinearMap.ker f ≤ K := by
  rw [show K = _ from f.iterateMapComap_eq_succ i K m heq hf hi 0]
  exact f.ker_le_comap

end LinearMap

