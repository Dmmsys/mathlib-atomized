/-
Copyright (c) 2023 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Yury Kudryashov, Lawrence Wu
-/
module

public import Mathlib.NumberTheory.Divisors
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic

/-!
# `Nat.divisors` as a multiplicative homomorphism

The main definition of this file is `Nat.divisorsHom : ℕ →* Finset ℕ`,
exhibiting `Nat.divisors` as a multiplicative homomorphism from `ℕ` to `Finset ℕ`.
-/

@[expose] public section

open Nat Finset
open scoped Pointwise

/-- The divisors of a product of natural numbers are the pointwise product of the divisors of the
factors. -/
/-
**Nat.divisors_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Nat.divisors_mul (m n : Nat) : divisors (m * n) = divisors m * divisors n
参数：m n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Nat.instIsDomain`：IsDomain ℕ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The divisors of a product of natural numbers are the pointwise product of the di
visors of the
factors.
-/
lemma Nat.divisors_mul (m n : ℕ) : divisors (m * n) = divisors m * divisors n := by
  ext k
  simp_rw [mem_mul, mem_divisors, Nat.dvd_mul, mul_ne_zero_iff, ← exists_and_left,
    ← exists_and_right]
  simp only [and_assoc, and_comm, and_left_comm]

/-- `Nat.divisors` as a `MonoidHom`. -/
@[simps]
/-
**Nat.divisorsHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Nat.divisorsHom : Nat ->* Finset Nat where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.divisors_one`：divisors_one : divisors 1 = {1}
· 使用引理 `Nat.divisors_mul`：Nat.divisors_mul (m n : Nat) : divisors (m * n) = divi
sors m * divisors n

--- 原说明 ---
`Nat.divisors` as a `MonoidHom`.
-/
def Nat.divisorsHom : ℕ →* Finset ℕ where
  toFun := Nat.divisors
  map_mul' := divisors_mul
  map_one' := divisors_one
/-
**Nat.Prime.divisors_sq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Nat.Prime.divisors_sq {p : Nat} (hp : p.Prime) : (p ^ 2).divisors = {p ^ 2
, p, 1}
参数：hp : p.Prime。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.pow_right_injective`：∀ {a : ℕ}, 2 ≤ a → Function.Injective fun x => 
a ^ x
· 使用定理 `Nat.Prime.two_le`：∀ {p : ℕ}, Nat.Prime p → 2 ≤ p
· 使用定理 `Nat.divisors_prime_pow`：divisors_prime_pow {p : Nat} (pp : p.Prime) (k :
 Nat) : divisors (p ^ k) = (Finset.range (k + 1)).map ⟨(p ^ ·), Nat.pow_right_in
jective pp.t…
· 使用定理 `Finset.range_add_one`：range_add_one : range (n + 1) = insert n (range n)
· 使用定理 `LawfulSingleton.insert_empty_eq`：∀ {α : Type u} {β : Type v} {inst : Emp
tyCollection β} {inst_1 : Insert α β} {inst_2 : Singleton α β}   [self : LawfulS
ingleton α β] (x : α)…
· 使用定理 `Finset.instLawfulSingleton`：∀ {α : Type u_1} [inst : DecidableEq α], Law
fulSingleton α (Finset α)
· 使用定理 `Finset.map_insert`：map_insert [DecidableEq α] [DecidableEq β] (f : α ↪ β
) (a : α) (s : Finset α) : (insert a s).map f = insert (f a) (s.map f)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Finset.map_singleton`：map_singleton (f : α ↪ β) (a : α) : map f {a} = {f
 a}
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Nat.Prime.divisors_sq {p : ℕ} (hp : p.Prime) : (p ^ 2).divisors = {p ^ 2, p, 1} := by
  simp [divisors_prime_pow hp, range_add_one]
/-
**List.nat_divisors_prod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：List.nat_divisors_prod (l : List Nat) : divisors l.prod = (l.map divisors)
.prod
参数：l : List Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_list_prod`：map_list_prod {F : Type*} [FunLike F M N] [MonoidHomClass
 F M N] (f : F) (l : List M) : f l.prod = (l.map f).prod
-/
lemma List.nat_divisors_prod (l : List ℕ) : divisors l.prod = (l.map divisors).prod :=
  map_list_prod Nat.divisorsHom l
/-
**Multiset.nat_divisors_prod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Multiset.nat_divisors_prod (s : Multiset Nat) : divisors s.prod = (s.map d
ivisors).prod
参数：s : Multiset Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_multiset_prod`：∀ {F : Type u_1} {M : Type u_5} {N : Type u_6} [inst 
: CommMonoid M] [inst_1 : CommMonoid N] [inst_2 : FunLike F M N]   [MonoidHomCla
ss F M …
-/
lemma Multiset.nat_divisors_prod (s : Multiset ℕ) : divisors s.prod = (s.map divisors).prod :=
  map_multiset_prod Nat.divisorsHom s
/-
**Finset.nat_divisors_prod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Finset.nat_divisors_prod {ι : Type*} (s : Finset ι) (f : ι -> Nat) : divis
ors (∏ i in s, f i) = ∏ i in s, divisors (f i)
参数：s : Finset ι；f : ι -> Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
-/
lemma Finset.nat_divisors_prod {ι : Type*} (s : Finset ι) (f : ι → ℕ) :
    divisors (∏ i ∈ s, f i) = ∏ i ∈ s, divisors (f i) :=
  map_prod Nat.divisorsHom f s

/-- Products of divisors taken from coprime naturals are unique. -/
/-
**Nat.Coprime.mul_injOn_divisors** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.Coprime.mul_injOn_divisors {m n : Nat} (hmn : m.Coprime n) : Set.InjOn
 (fun p : Nat × Nat => p.1 * p.2) ↑(divisors m ×ˢ divisors n)
参数：hmn : m.Coprime n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dvd_antisymm`：dvd_antisymm : a ∣ b -> b ∣ a -> a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Nat.Coprime.dvd_of_dvd_mul_right`：∀ {k n m : ℕ}, k.Coprime n → k ∣ m * n
 → k ∣ m
· 使用定理 `Nat.Coprime.coprime_dvd_right`：∀ {n m k : ℕ}, n ∣ m → k.Coprime m → k.Co
prime n
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.Coprime.coprime_dvd_left`：∀ {m k n : ℕ}, m ∣ k → k.Coprime n → m.Cop
rime n
· 使用定理 `Nat.dvd_mul_right`：∀ (a b : ℕ), a ∣ a * b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `Nat.mul_right_inj`：∀ {a b c : ℕ}, a ≠ 0 → (a * b = a * c ↔ b = c)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False

--- 原说明 ---
Products of divisors taken from coprime naturals are unique.
-/
theorem Nat.Coprime.mul_injOn_divisors {m n : ℕ} (hmn : m.Coprime n) :
    Set.InjOn (fun p : ℕ × ℕ ↦ p.1 * p.2) ↑(divisors m ×ˢ divisors n) := by
  rintro ⟨dm₁, dn₁⟩ h₁ ⟨dm₂, dn₂⟩ h₂ hd
  simp only [Finset.mem_coe, Finset.mem_product, mem_divisors] at *
  suffices dm₁ = dm₂ from Prod.ext this <| by
    rwa [this, Nat.mul_right_inj (by simp [·] at h₂)] at hd
  exact dvd_antisymm
    (hmn.coprime_dvd_left h₁.1.1 |>.coprime_dvd_right h₂.2.1
      |>.dvd_of_dvd_mul_right (hd ▸ dm₁.dvd_mul_right dn₁))
    (hmn.coprime_dvd_left h₂.1.1 |>.coprime_dvd_right h₁.2.1
      |>.dvd_of_dvd_mul_right (hd ▸ dm₂.dvd_mul_right dn₂))

/-- A variant of `Nat.divisors_mul` with a more structured RHS. -/
/-
**Nat.Coprime.divisors_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.Coprime.divisors_mul {m n : Nat} (hmn : m.Coprime n) : divisors (m * n
) = (divisors m ×ˢ divisors n).attach.map ⟨fun p => p.val.1 * p.val.2, fun i j h
xy => Subtype.ext hmn.mul_injOn_divisors i.prop j.prop hxy⟩
参数：hmn : m.Coprime n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Nat.Coprime.mul_injOn_divisors`：Nat.Coprime.mul_injOn_divisors {m n : Na
t} (hmn : m.Coprime n) : Set.InjOn (fun p : Nat × Nat => p.1 * p.2) ↑(divisors m
 ×ˢ divisors n)
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.attach_image_val`：attach_image_val [DecidableEq α] {s : Finset α}
 : s.attach.image Subtype.val = s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.mul_def`：mul_def : s * t = (s ×ˢ t).image fun p : α × α => p.1 * 
p.2
· 使用引理 `Nat.divisors_mul`：Nat.divisors_mul (m n : Nat) : divisors (m * n) = divi
sors m * divisors n
· 使用定理 `Finset.map_eq_image`：map_eq_image (f : α ↪ β) (s : Finset α) : s.map f =
 s.image f
· 使用定理 `Finset.image_image`：image_image [DecidableEq γ] {g : β -> γ} : (s.image 
f).image g = s.image (g ∘ f)

--- 原说明 ---
A variant of `Nat.divisors_mul` with a more structured RHS.
-/
theorem Nat.Coprime.divisors_mul {m n : ℕ} (hmn : m.Coprime n) :
    divisors (m * n) = (divisors m ×ˢ divisors n).attach.map
      ⟨fun p => p.val.1 * p.val.2,
        fun i j hxy => Subtype.ext <| hmn.mul_injOn_divisors i.prop j.prop hxy⟩ := calc
  _ = ((divisors m ×ˢ divisors n).attach.image Subtype.val).image fun p ↦ p.1 * p.2 := by
    rw [Finset.attach_image_val, ← Finset.mul_def, Nat.divisors_mul]
  _ = _ := by rw [Finset.map_eq_image, Finset.image_image]; rfl
