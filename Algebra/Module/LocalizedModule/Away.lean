/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Basic

/-!
# API for localized modules away from an element

We provide some specialized API for the localization of a module away from an element.
-/

public section

namespace IsLocalizedModule.Away

variable {R : Type*} [CommSemiring R] {M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
  [Module R M] [Module R N] {f : M →ₗ[R] N} {r : R}

/-
**IsLocalizedModule.Away.mk** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalizedModule.Away`。
形式化陈述：mk (h₁ : IsUnit (algebraMap R (Module.End R N) r)) (h₂ : forall (x : N), e
xists (n : Nat) (y : M), r ^ n • x = f y) (h₃ : forall (x y : M), f x = f y -> e
xists (n : Nat), r ^ n • x = r ^ n • y) : IsLocalizedModule.Away r f where map_u
nits
参数：h₁ : IsUnit (algebraMap R (Module.End R N) r)；h₂ : forall (x : N), exists (n 
: Nat) (y : M), r ^ n • x = f y；h₃ : forall (x y : M), f x = f y -> exists (n : 
Nat), r ^ n • x = r ^ n • y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `IsUnit.pow`：∀ {M : Type u_1} [inst : Monoid M] {a : M} (n : ℕ), IsUnit a
 → IsUnit (a ^ n)
-/
lemma mk (h₁ : IsUnit (algebraMap R (Module.End R N) r))
    (h₂ : ∀ (x : N), ∃ (n : ℕ) (y : M), r ^ n • x = f y)
    (h₃ : ∀ (x y : M), f x = f y → ∃ (n : ℕ), r ^ n • x = r ^ n • y) :
    IsLocalizedModule.Away r f where
  map_units := fun ⟨_, ⟨n, rfl⟩⟩ ↦ by simp [h₁.pow]
  surj x := by
    obtain ⟨n, y, hy⟩ := h₂ x
    use ⟨y, ⟨_, n, rfl⟩⟩, hy
  exists_of_eq {x y} hxy := by
    obtain ⟨n, hn⟩ := h₃ _ _ hxy
    use ⟨_, n, rfl⟩, hn
/-
**IsLocalizedModule.Away.mk_of_addCommGroup** 是 Mathlib 中的一个引理，位于命名空间 `IsLocaliz
edModule.Away`。
形式化陈述：mk_of_addCommGroup {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module
 R M] [Module R N] {f : M ->ₗ[R] N} {r : R} (h₁ : IsUnit (algebraMap R (Module.E
nd R N) r)) (h₂ : forall (x : N), exists (n : Nat) (y : M), r ^ n • x = f y) (h₃
 : forall (x : M), f x = 0 -> exists (n : Nat), r ^ n • x = 0) : IsLocalizedModu
le.Away r f
参数：h₁ : IsUnit (algebraMap R (Module.End R N) r)；h₂ : forall (x : N), exists (n 
: Nat) (y : M), r ^ n • x = f y；h₃ : forall (x : M), f x = 0 -> exists (n : Nat)
, r ^ n • x = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalizedModule.Away.mk`：mk (h₁ : IsUnit (algebraMap R (Module.End R N
) r)) (h₂ : forall (x : N), exists (n : Nat) (y : M), r ^ n • x = f y) (h₃ : for
all (x y : M), …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
-/
lemma mk_of_addCommGroup {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    {f : M →ₗ[R] N} {r : R} (h₁ : IsUnit (algebraMap R (Module.End R N) r))
    (h₂ : ∀ (x : N), ∃ (n : ℕ) (y : M), r ^ n • x = f y)
    (h₃ : ∀ (x : M), f x = 0 → ∃ (n : ℕ), r ^ n • x = 0) :
    IsLocalizedModule.Away r f := by
  refine IsLocalizedModule.Away.mk h₁ h₂ fun x y hxy ↦ ?_
  have : f (x - y) = 0 := by simp [hxy]
  obtain ⟨n, hn⟩ := h₃ _ this
  use n
  simpa [smul_sub, sub_eq_zero] using hn

variable (r) [IsLocalizedModule.Away r f]

variable (f) in
include f in
/-
**IsLocalizedModule.Away.isUnit_algebraMap** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalize
dModule.Away`。
形式化陈述：isUnit_algebraMap : IsUnit (algebraMap R (Module.End R N) r)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalizedModule.map_units`：∀ {R : Type u_1} {inst : CommSemiring R} {M
 : Type u_2} {M' : Type u_3} {inst_1 : AddCommMonoid M}   {inst_2 : AddCommMonoi
d M'} {inst_3 : _…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isUnit_algebraMap : IsUnit (algebraMap R (Module.End R N) r) :=
  IsLocalizedModule.map_units (S := .powers r) f ⟨_, 1, by simp⟩
/-
**IsLocalizedModule.Away.exists_of_eq** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalizedModu
le.Away`。
形式化陈述：exists_of_eq {x y : M} (h : f x = f y) : exists (n : Nat), r ^ n • x = r ^
 n • y
参数：h : f x = f y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalizedModule.exists_of_eq`：∀ {R : Type u_1} {inst : CommSemiring R}
 {M : Type u_2} {M' : Type u_3} {inst_1 : AddCommMonoid M}   {inst_2 : AddCommMo
noid M'} {inst_3 : _…
-/
lemma exists_of_eq {x y : M} (h : f x = f y) : ∃ (n : ℕ), r ^ n • x = r ^ n • y := by
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := IsLocalizedModule.exists_of_eq (S := .powers r) h
  use n, hn

variable (f) in
/-
**IsLocalizedModule.Away.surj** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalizedModule.Away`
。
形式化陈述：surj (y : N) : exists (n : Nat) (x : M), r ^ n • y = f x
参数：y : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalizedModule.surj`：∀ {R : Type u_1} {inst : CommSemiring R} {M : Ty
pe u_2} {M' : Type u_3} {inst_1 : AddCommMonoid M}   {inst_2 : AddCommMonoid M'}
 {inst_3 : _…
-/
lemma surj (y : N) : ∃ (n : ℕ) (x : M), r ^ n • y = f x := by
  obtain ⟨⟨x, ⟨_, n, rfl⟩⟩, h⟩ := IsLocalizedModule.surj (S := .powers r) f y
  use n, x, h
/-
**IsLocalizedModule.Away.of_associated** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalizedMod
ule.Away`。
形式化陈述：of_associated {r r' : R} (h : Associated r r') [IsLocalizedModule.Away r f
] : IsLocalizedModule.Away r' f
参数：h : Associated r r'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `IsLocalizedModule.Away.mk`：mk (h₁ : IsUnit (algebraMap R (Module.End R N
) r)) (h₂ : forall (x : N), exists (n : Nat) (y : M), r ^ n • x = f y) (h₃ : for
all (x y : M), …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `IsLocalizedModule.Away.isUnit_algebraMap`：isUnit_algebraMap : IsUnit (al
gebraMap R (Module.End R N) r)
· 使用引理 `IsLocalizedModule.Away.surj`：surj (y : N) : exists (n : Nat) (x : M), r 
^ n • y = f x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `IsLocalizedModule.Away.exists_of_eq`：exists_of_eq {x y : M} (h : f x = f
 y) : exists (n : Nat), r ^ n • x = r ^ n • y
-/
lemma of_associated {r r' : R} (h : Associated r r') [IsLocalizedModule.Away r f] :
    IsLocalizedModule.Away r' f := by
  obtain ⟨u, rfl⟩ := h
  rw [mul_comm]
  refine .mk ?_ ?_ ?_
  · simp [IsUnit.mul, isUnit_algebraMap f r, u.isUnit.map _]
  · intro y
    obtain ⟨n, x, hx⟩ := surj f r y
    use n, (u ^ n) • x
    simp [mul_pow, ← hx, mul_smul, Units.smul_def]
  · intro x y hxy
    obtain ⟨n, hn⟩ := exists_of_eq r hxy
    use n
    simp [mul_pow, mul_smul, hn]
/-
**IsLocalizedModule.Away.iff_of_associated** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalize
dModule.Away`。
形式化陈述：iff_of_associated {r r' : R} (h : Associated r r') : IsLocalizedModule.Awa
y r f ↔ IsLocalizedModule.Away r' f
参数：h : Associated r r'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalizedModule.Away.of_associated`：of_associated {r r' : R} (h : Asso
ciated r r') [IsLocalizedModule.Away r f] : IsLocalizedModule.Away r' f
· 使用定理 `Associated.symm`：∀ {M : Type u_1} [inst : Monoid M] {x y : M}, Associate
d x y → Associated y x
-/
lemma iff_of_associated {r r' : R} (h : Associated r r') :
    IsLocalizedModule.Away r f ↔ IsLocalizedModule.Away r' f :=
  ⟨fun _ ↦ .of_associated h, fun _ ↦ .of_associated h.symm⟩

end IsLocalizedModule.Away

