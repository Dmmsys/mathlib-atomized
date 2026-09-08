/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Ring Homomorphisms surjective on stalks

In this file, we prove some results on ring homomorphisms surjective on stalks, to be used in
the development of immersions in algebraic geometry.

A ring homomorphism `R →+* S` is surjective on stalks if `R_p →+* S_q` is surjective for all pairs
of primes `p = f⁻¹(q)`. We show that this property is stable under composition and base change, and
that surjections and localizations satisfy this.

-/

@[expose] public section

variable {R : Type*} [CommRing R] (M : Submonoid R) {S : Type*} [CommRing S]
variable {T : Type*} [CommRing T]
variable {g : S →+* T} {f : R →+* S}

namespace RingHom

/--
A ring homomorphism `R →+* S` is surjective on stalks if `R_p →+* S_q` is surjective for all pairs
of primes `p = f⁻¹(q)`.
-/
/-
**RingHom.SurjectiveOnStalks** 是 Mathlib 中的一个定义，位于命名空间 `RingHom`。
形式化陈述：SurjectiveOnStalks (f : R ->+* S) : Prop
参数：f : R ->+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A ring homomorphism `R →+* S` is surjective on stalks if `R_p →+* S_q` is surjec
tive for all pairs
of primes `p = f⁻¹(q)`.
-/
def SurjectiveOnStalks (f : R →+* S) : Prop :=
  ∀ (P : Ideal S) (_ : P.IsPrime), Function.Surjective (Localization.localRingHom _ P f rfl)

/--
`R_p →+* S_q` is surjective if and only if
every `x : S` is of the form `f x / f r` for some `f r ∉ q`.
This is useful when proving `SurjectiveOnStalks`.
-/
/-
**RingHom.surjective_localRingHom_iff** 是 Mathlib 中的一个引理，位于命名空间 `RingHom`。
形式化陈述：surjective_localRingHom_iff (P : Ideal S) [P.IsPrime] : Function.Surjectiv
e (Localization.localRingHom _ P f rfl) ↔ forall s : S, exists x r : R, exists c
 ∉ P, f r ∉ P ∧ c * f r * s = c * f x
参数：P : Ideal S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsPrime.comap`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : 
Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f : F)   {K : Ideal 
S} [inst_…
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.exists_mk'_eq`：∀ {R : Type u_1} [inst : CommSemiring R] (
M : Submonoid R) {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Localization.le_comap_primeCompl_iff`：le_comap_primeCompl_iff {J : Ideal
 P} [J.IsPrime] {f : R ->+* P} : I.primeCompl <= J.primeCompl.comap f ↔ J.comap 
f <= I
· 使用定理 `ge_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalization.eq_iff_exists`：eq_iff_exists {x y} : algebraMap R S x = a
lgebraMap R S y ↔ exists c : M, ↑c * x = ↑c * y
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Submonoid.coe_one`：coe_one : ((1 : S) : M) = 1
· 使用定理 `IsLocalization.mk'_eq_iff_eq`：∀ {R : Type u_1} [inst : CommSemiring R] {
M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…
· 使用定理 `Localization.localRingHom_mk'`：localRingHom_mk' (J : Ideal P) [J.IsPrime
] (f : R ->+* P) (hIJ : I = J.comap f) (x : R) (y : I.primeCompl) : localRingHom
 I J f hIJ (IsLocal…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Localization.ind`：ind {p : Localization S -> Prop} (H : forall y : M × S
, p (mk y.1 y.2)) (x) : p x
· 使用定理 `Submonoid.mul_mem`：∀ {M : Type u_1} [inst : MulOneClass M] (S : Submonoi
d M) {x y : M}, x ∈ S → y ∈ S → x * y ∈ S
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `Ideal.mul_mem_left`：mul_mem_left : b in I -> a * b in I
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Localization.mk_eq_mk'`：mk_eq_mk'_apply (x y) : mk x y = IsLocalization.
mk' (Localization M) x y
· 使用定理 `IsLocalization.mk'.congr_simp`：∀ {R : Type u_1} [inst : CommSemiring R] 
{M : Submonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R
 S] [inst_3 : IsLoc…
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
（共 44 条，此处仅展示前 30 条）

--- 原说明 ---
`R_p →+* S_q` is surjective if and only if
every `x : S` is of the form `f x / f r` for some `f r ∉ q`.
This is useful when proving `SurjectiveOnStalks`.
-/
lemma surjective_localRingHom_iff (P : Ideal S) [P.IsPrime] :
    Function.Surjective (Localization.localRingHom _ P f rfl) ↔
      ∀ s : S, ∃ x r : R, ∃ c ∉ P, f r ∉ P ∧ c * f r * s = c * f x := by
  constructor
  · intro H y
    obtain ⟨a, ha⟩ := H (IsLocalization.mk' _ y (1 : P.primeCompl))
    obtain ⟨a, t, rfl⟩ := IsLocalization.exists_mk'_eq (P.comap f).primeCompl a
    rw [Localization.localRingHom_mk', IsLocalization.mk'_eq_iff_eq,
      Submonoid.coe_one, one_mul, IsLocalization.eq_iff_exists P.primeCompl] at ha
    obtain ⟨c, hc⟩ := ha
    simp only [← mul_assoc] at hc
    exact ⟨_, _, _, c.2, t.2, hc.symm⟩
  · refine fun H y ↦ Localization.ind (fun ⟨y, t, h⟩ ↦ ?_) y
    simp only
    obtain ⟨yx, ys, yc, hyc, hy, ey⟩ := H y
    obtain ⟨tx, ts, yt, hyt, ht, et⟩ := H t
    refine ⟨Localization.mk (yx * ts) ⟨ys * tx, Submonoid.mul_mem _ hy ?_⟩, ?_⟩
    · exact fun H ↦ mul_mem (P.primeCompl.mul_mem hyt ht) h (et ▸ Ideal.mul_mem_left _ yt H)
    · simp only [Localization.mk_eq_mk', Localization.localRingHom_mk', map_mul f,
        IsLocalization.mk'_eq_iff_eq, IsLocalization.eq_iff_exists P.primeCompl]
      refine ⟨⟨yc, hyc⟩ * ⟨yt, hyt⟩, ?_⟩
      simp only [Submonoid.coe_mul]
      convert! congr($(ey.symm) * $(et)) using 1 <;> ring
/-
**RingHom.surjectiveOnStalks_iff_forall_ideal** 是 Mathlib 中的一个引理，位于命名空间 `RingHom
`。
形式化陈述：surjectiveOnStalks_iff_forall_ideal : f.SurjectiveOnStalks ↔ forall I : Id
eal S, I != ⊤ -> forall s : S, exists x r : R, exists c ∉ I, f r ∉ I ∧ c * f r *
 s = c * f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Ideal.IsPrime.comap`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : 
Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f : F)   {K : Ideal 
S} [inst_…
· 使用定理 `Ideal.exists_le_maximal`：exists_le_maximal (I : Ideal α) (hI : I != ⊤) :
 exists M : Ideal α, M.IsMaximal ∧ I <= M
· 使用定理 `Ideal.IsMaximal.isPrime`：∀ {α : Type u} [inst : CommSemiring α] {I : Ide
al α}, I.IsMaximal → I.IsPrime
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
-/
lemma surjectiveOnStalks_iff_forall_ideal :
    f.SurjectiveOnStalks ↔
      ∀ I : Ideal S, I ≠ ⊤ → ∀ s : S, ∃ x r : R, ∃ c ∉ I, f r ∉ I ∧ c * f r * s = c * f x := by
  simp_rw [SurjectiveOnStalks, surjective_localRingHom_iff]
  refine ⟨fun H I hI s ↦ ?_, fun H I hI ↦ H I hI.ne_top⟩
  obtain ⟨M, hM, hIM⟩ := I.exists_le_maximal hI
  obtain ⟨x, r, c, hc, hr, e⟩ := H M hM.isPrime s
  exact ⟨x, r, c, fun h ↦ hc (hIM h), fun h ↦ hr (hIM h), e⟩
/-
**RingHom.surjectiveOnStalks_iff_forall_maximal** 是 Mathlib 中的一个引理，位于命名空间 `RingH
om`。
形式化陈述：surjectiveOnStalks_iff_forall_maximal : f.SurjectiveOnStalks ↔ forall (I :
 Ideal S) (_ : I.IsMaximal), Function.Surjective (Localization.localRingHom _ I 
f rfl)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsPrime.comap`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : 
Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f : F)   {K : Ideal 
S} [inst_…
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `Ideal.IsMaximal.isPrime`：∀ {α : Type u} [inst : CommSemiring α] {I : Ide
al α}, I.IsMaximal → I.IsPrime
· 使用定理 `Ideal.exists_le_maximal`：exists_le_maximal (I : Ideal α) (hI : I != ⊤) :
 exists M : Ideal α, M.IsMaximal ∧ I <= M
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
lemma surjectiveOnStalks_iff_forall_maximal :
    f.SurjectiveOnStalks ↔ ∀ (I : Ideal S) (_ : I.IsMaximal),
      Function.Surjective (Localization.localRingHom _ I f rfl) := by
  refine ⟨fun H I hI ↦ H I hI.isPrime, fun H I hI ↦ ?_⟩
  simp_rw [surjective_localRingHom_iff] at H ⊢
  intro s
  obtain ⟨M, hM, hIM⟩ := I.exists_le_maximal hI.ne_top
  obtain ⟨x, r, c, hc, hr, e⟩ := H M hM s
  exact ⟨x, r, c, fun h ↦ hc (hIM h), fun h ↦ hr (hIM h), e⟩
/-
**RingHom.surjectiveOnStalks_iff_forall_maximal'** 是 Mathlib 中的一个引理，位于命名空间 `Ring
Hom`。
形式化陈述：surjectiveOnStalks_iff_forall_maximal' : f.SurjectiveOnStalks ↔ forall I :
 Ideal S, I.IsMaximal -> forall s : S, exists x r : R, exists c ∉ I, f r ∉ I ∧ c
 * f r * s = c * f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.IsPrime.comap`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : 
Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f : F)   {K : Ideal 
S} [inst_…
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma surjectiveOnStalks_iff_forall_maximal' :
    f.SurjectiveOnStalks ↔ ∀ I : Ideal S, I.IsMaximal →
      ∀ s : S, ∃ x r : R, ∃ c ∉ I, f r ∉ I ∧ c * f r * s = c * f x := by
  simp only [surjectiveOnStalks_iff_forall_maximal, surjective_localRingHom_iff]
/-
**RingHom.surjectiveOnStalks_of_exists_div** 是 Mathlib 中的一个引理，位于命名空间 `RingHom`。
形式化陈述：surjectiveOnStalks_of_exists_div (h : forall x : S, exists r s : R, IsUnit
 (f s) ∧ f s * x = f r) : SurjectiveOnStalks f
参数：h : forall x : S, exists r s : R, IsUnit (f s) ∧ f s * x = f r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `RingHom.surjectiveOnStalks_iff_forall_ideal`：surjectiveOnStalks_iff_fora
ll_ideal : f.SurjectiveOnStalks ↔ forall I : Ideal S, I != ⊤ -> forall s : S, ex
ists x r : R, exists c ∉ I, f r ∉…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.eq_top_of_isUnit_mem`：eq_top_of_isUnit_mem {x} (hx : x in I) (h : 
IsUnit x) : I = ⊤
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
lemma surjectiveOnStalks_of_exists_div (h : ∀ x : S, ∃ r s : R, IsUnit (f s) ∧ f s * x = f r) :
    SurjectiveOnStalks f :=
  surjectiveOnStalks_iff_forall_ideal.mpr fun I hI x ↦
    let ⟨r, s, hr, hr'⟩ := h x
    ⟨r, s, 1, by simpa [← Ideal.eq_top_iff_one], fun h ↦ hI (I.eq_top_of_isUnit_mem h hr), by simpa⟩
/-
**RingHom.surjectiveOnStalks_of_surjective** 是 Mathlib 中的一个引理，位于命名空间 `RingHom`。
形式化陈述：surjectiveOnStalks_of_surjective (h : Function.Surjective f) : SurjectiveO
nStalks f
参数：h : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `RingHom.surjectiveOnStalks_iff_forall_ideal`：surjectiveOnStalks_iff_fora
ll_ideal : f.SurjectiveOnStalks ↔ forall I : Ideal S, I != ⊤ -> forall s : S, ex
ists x r : R, exists c ∉ I, f r ∉…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma surjectiveOnStalks_of_surjective (h : Function.Surjective f) :
    SurjectiveOnStalks f :=
  surjectiveOnStalks_iff_forall_ideal.mpr fun _ _ s ↦
    let ⟨r, hr⟩ := h s
    ⟨r, 1, 1, by simpa [← Ideal.eq_top_iff_one], by simpa [← Ideal.eq_top_iff_one], by simp [hr]⟩
/-
**RingHom._root_.RingEquiv.surjectiveOnStalks** 是 Mathlib 中的一个引理，位于命名空间 `RingHom
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.RingEquiv.surjectiveOnStalks (e : R ≃+* S) :
    e.toRingHom.SurjectiveOnStalks :=
  RingHom.surjectiveOnStalks_of_surjective e.surjective
/-
**RingHom.SurjectiveOnStalks.comp** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.SurjectiveO
nStalks`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {S : Type u_2} [inst_1 : CommRing S] 
{T : Type u_3} [inst_2 : CommRing T]   {g : S →+* T} {f : R →+* S}, g.Surjective
OnStalks → f.SurjectiveOnStalks → (g.comp f).SurjectiveOnStalks
参数：g.comp f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsPrime.comap`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : 
Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f : F)   {K : Ideal 
S} [inst_…
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Localization.localRingHom_comp`：localRingHom_comp {S : Type*} [CommSemir
ing S] (J : Ideal S) [hJ : J.IsPrime] (K : Ideal P) [hK : K.IsPrime] (f : R ->+*
 S) (hIJ : I = J.com…
· 使用定理 `RingHom.coe_comp`：coe_comp (hnp : β ->+* γ) (hmn : α ->+* β) : (hnp.comp
 hmn : α -> γ) = hnp ∘ hmn
-/
lemma SurjectiveOnStalks.comp (hg : SurjectiveOnStalks g) (hf : SurjectiveOnStalks f) :
    SurjectiveOnStalks (g.comp f) := by
  intro I hI
  have := (hg I hI).comp (hf _ (hI.comap g))
  rwa [← RingHom.coe_comp, ← Localization.localRingHom_comp] at this
/-
**RingHom.SurjectiveOnStalks.of_comp** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.Surjecti
veOnStalks`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {S : Type u_2} [inst_1 : CommRing S] 
{T : Type u_3} [inst_2 : CommRing T]   {g : S →+* T} {f : R →+* S}, (g.comp f).S
urjectiveOnStalks → g.SurjectiveOnStalks
参数：g.comp f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u
_3} {f : α → β} {g : γ → α},   Function.Surjective (f ∘ g) → Function.Surjective
 f
· 使用定理 `Ideal.IsPrime.comap`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : 
Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f : F)   {K : Ideal 
S} [inst_…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.coe_comp`：coe_comp (hnp : β ->+* γ) (hmn : α ->+* β) : (hnp.comp
 hmn : α -> γ) = hnp ∘ hmn
· 使用定理 `Localization.localRingHom_comp`：localRingHom_comp {S : Type*} [CommSemir
ing S] (J : Ideal S) [hJ : J.IsPrime] (K : Ideal P) [hK : K.IsPrime] (f : R ->+*
 S) (hIJ : I = J.com…
-/
lemma SurjectiveOnStalks.of_comp (hg : SurjectiveOnStalks (g.comp f)) :
    SurjectiveOnStalks g := by
  intro I hI
  have := hg I hI
  rw [Localization.localRingHom_comp (I.comap (g.comp f)) (I.comap g) _ _ rfl _ rfl,
    RingHom.coe_comp] at this
  exact this.of_comp
/-
**RingHom.SurjectiveOnStalks.localRingHom_surjective** 是 Mathlib 中的一个定理，位于命名空间 `
RingHom.SurjectiveOnStalks`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {S : Type u_2} [inst_1 : CommRing S] 
{f : R →+* S},   f.SurjectiveOnStalks →     ∀ (P : Ideal R) [inst_2 : P.IsPrime]
 (Q : Ideal S) [inst_3 : Q.IsPrime] (e : P = Ideal.comap f Q),       Function.Su
rjective ⇑(Localization.localRingHom P Q f e)
参数：P : Ideal R；Q : Ideal S；e : P = Ideal.comap f Q；Localization.localRingHom P Q
 f e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma SurjectiveOnStalks.localRingHom_surjective (hf : SurjectiveOnStalks f)
    (P : Ideal R) [P.IsPrime] (Q : Ideal S) [Q.IsPrime] (e : P = Q.comap f) :
    Function.Surjective (Localization.localRingHom P Q f e) :=
  e ▸ hf Q _

open TensorProduct

variable [Algebra R T] [Algebra R S] in
/--
If `R → T` is surjective on stalks, and `J` is some prime of `T`,
then every element `x` in `S ⊗[R] T` satisfies `(1 ⊗ r • t) * x = a ⊗ t` for some
`r : R`, `a : S`, and `t : T` such that `r • t ∉ J`.
-/
/-
**RingHom.SurjectiveOnStalks.exists_mul_eq_tmul** 是 Mathlib 中的一个定理，位于命名空间 `RingH
om.SurjectiveOnStalks`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {S : Type u_2} [inst_1 : CommRing S] 
{T : Type u_3} [inst_2 : CommRing T]   [inst_3 : Algebra R T] [inst_4 : Algebra 
R S],   (algebraMap R T).SurjectiveOnStalks →     ∀ (x : TensorProduct R S T) (J
 : Ideal T), J.IsPrime → ∃ t r a, r • t ∉ J ∧ 1 ⊗ₜ[R] (r • t) * x = a ⊗ₜ[R] t
参数：algebraMap R T；x : TensorProduct R S T；J : Ideal T；r • t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Submonoid.one_mem`：∀ {M : Type u_1} [inst : MulOneClass M] (S : Submonoi
d M), 1 ∈ S
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `TensorProduct.zero_tmul`：zero_tmul (n : N) : (0 : M) otimesₜ[R] n = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.IsPrime.comap`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : 
Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f : F)   {K : Ideal 
S} [inst_…
· 使用引理 `RingHom.surjective_localRingHom_iff`：surjective_localRingHom_iff (P : Id
eal S) [P.IsPrime] : Function.Surjective (Localization.localRingHom _ P f rfl) ↔
 forall s : S, exists x r…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submonoid.mul_mem`：∀ {M : Type u_1} [inst : MulOneClass M] (S : Submonoi
d M) {x y : M}, x ∈ S → y ∈ S → x * y ∈ S
· 使用定理 `Algebra.TensorProduct.tmul_mul_tmul`：tmul_mul_tmul (a₁ a₂ : A) (b₁ b₂ : 
B) : a₁ otimesₜ[R] b₁ * a₂ otimesₜ[R] b₂ = (a₁ * a₂) otimesₜ[R] (b₁ * b₂)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `TensorProduct.smul_tmul`：smul_tmul [DistribMulAction R' N] [CompatibleSM
ul R R' M N] (r : R') (m : M) (n : N) : (r • m) otimesₜ n = m otimesₜ[R] (r • n)
· 使用定理 `TensorProduct.CompatibleSMul.isScalarTower`：∀ {R : Type u_1} {R' : Type 
u_4} [inst : CommSemiring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8} 
  [inst_2 : AddCommMonoid M] [in…
· 使用引理 `smul_smul_smul_comm`：smul_smul_smul_comm [SMul α β] [SMul α γ] [SMul β δ
] [SMul α δ] [SMul γ δ] [IsScalarTower α β δ] [IsScalarTower α γ δ] [SMulCommCla
ss β γ δ]…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
· 使用定理 `TensorProduct.add_tmul`：add_tmul (m₁ m₂ : M) (n : N) : (m₁ + m₂) otimesₜ
 n = m₁ otimesₜ n + m₂ otimesₜ[R] n

--- 原说明 ---
If `R → T` is surjective on stalks, and `J` is some prime of `T`,
then every element `x` in `S ⊗[R] T` satisfies `(1 ⊗ r • t) * x = a ⊗ t` for som
e
`r : R`, `a : S`, and `t : T` such that `r • t ∉ J`.
-/
lemma SurjectiveOnStalks.exists_mul_eq_tmul
    (hf₂ : (algebraMap R T).SurjectiveOnStalks)
    (x : S ⊗[R] T) (J : Ideal T) (hJ : J.IsPrime) :
    ∃ (t : T) (r : R) (a : S), (r • t ∉ J) ∧
      (1 : S) ⊗ₜ[R] (r • t) * x = a ⊗ₜ[R] t := by
  induction x with
  | zero =>
    exact ⟨1, 1, 0, by rw [one_smul]; exact J.primeCompl.one_mem,
      by rw [mul_zero, TensorProduct.zero_tmul]⟩
  | tmul x₁ x₂ =>
    obtain ⟨y, s, c, hs, hc, e⟩ := (surjective_localRingHom_iff _).mp (hf₂ J hJ) x₂
    simp_rw [Algebra.smul_def]
    refine ⟨c, s, y • x₁, J.primeCompl.mul_mem hc hs, ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm _ c, e,
      TensorProduct.smul_tmul, Algebra.smul_def, mul_comm]
  | add x₁ x₂ hx₁ hx₂ =>
    obtain ⟨t₁, r₁, a₁, hr₁, e₁⟩ := hx₁
    obtain ⟨t₂, r₂, a₂, hr₂, e₂⟩ := hx₂
    have : (r₁ * r₂) • (t₁ * t₂) = (r₁ • t₁) * (r₂ • t₂) := by
      simp_rw [← smul_eq_mul]; rw [smul_smul_smul_comm]
    refine ⟨t₁ * t₂, r₁ * r₂, r₂ • a₁ + r₁ • a₂, this.symm ▸ J.primeCompl.mul_mem hr₁ hr₂, ?_⟩
    rw [this, ← one_mul (1 : S), ← Algebra.TensorProduct.tmul_mul_tmul, mul_add, mul_comm (_ ⊗ₜ _),
      mul_assoc, e₁, Algebra.TensorProduct.tmul_mul_tmul, one_mul, smul_mul_assoc,
      ← TensorProduct.smul_tmul, mul_comm (_ ⊗ₜ _), mul_assoc, e₂,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, smul_mul_assoc, ← TensorProduct.smul_tmul,
      TensorProduct.add_tmul, mul_comm t₁ t₂]

variable (S) in
/-
**RingHom.surjectiveOnStalks_of_isLocalization** 是 Mathlib 中的一个引理，位于命名空间 `RingHo
m`。
形式化陈述：surjectiveOnStalks_of_isLocalization [Algebra R S] [IsLocalization M S] : 
SurjectiveOnStalks (algebraMap R S)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RingHom.surjectiveOnStalks_of_exists_div`：surjectiveOnStalks_of_exists_d
iv (h : forall x : S, exists r s : R, IsUnit (f s) ∧ f s * x = f r) : Surjective
OnStalks f
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.exists_mk'_eq`：∀ {R : Type u_1} [inst : CommSemiring R] (
M : Submonoid R) {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…
· 使用定理 `IsLocalization.map_units`：map_units : forall y : M, IsUnit (algebraMap R
 S y)
· 使用定理 `IsLocalization.mk'_spec'`：∀ {R : Type u_1} [inst : CommSemiring R] {M : 
Submonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [
inst_3 : IsLoc…
-/
lemma surjectiveOnStalks_of_isLocalization
    [Algebra R S] [IsLocalization M S] :
    SurjectiveOnStalks (algebraMap R S) := by
  refine surjectiveOnStalks_of_exists_div fun s ↦ ?_
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq M s
  exact ⟨x, s, IsLocalization.map_units S s, IsLocalization.mk'_spec' S x s⟩
/-
**RingHom.SurjectiveOnStalks.baseChange** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.Surje
ctiveOnStalks`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {S : Type u_2} [inst_1 : CommRing S] 
{T : Type u_3} [inst_2 : CommRing T]   [inst_3 : Algebra R T] [inst_4 : Algebra 
R S],   (algebraMap R T).SurjectiveOnStalks → (algebraMap S (TensorProduct R S T
)).SurjectiveOnStalks
参数：algebraMap R T；algebraMap S (TensorProduct R S T)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.IsPrime.comap`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : 
Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f : F)   {K : Ideal 
S} [inst_…
· 使用引理 `RingHom.surjective_localRingHom_iff`：surjective_localRingHom_iff (P : Id
eal S) [P.IsPrime] : Function.Surjective (Localization.localRingHom _ P f rfl) ↔
 forall s : S, exists x r…
· 使用定理 `RingHom.SurjectiveOnStalks.exists_mul_eq_tmul`：∀ {R : Type u_1} [inst : 
CommRing R] {S : Type u_2} [inst_1 : CommRing S] {T : Type u_3} [inst_2 : CommRi
ng T]   [inst_3 : Algebra R T] [ins…
· 使用定理 `RingHom.map_mul`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β) (a b : α),   f (a * b) = f a * f b
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `Ideal.mem_comap`：mem_comap [RingHomClass F R S] {x} : x in comap f K ↔ f
 x in K
· 使用定理 `Ideal.mul_mem_right`：mul_mem_right {α} {a : α} (b : α) [Semiring α] (I :
 Ideal α) [I.IsTwoSided] (h : a in I) : a * b in I
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用定理 `TensorProduct.smul_tmul`：smul_tmul [DistribMulAction R' N] [CompatibleSM
ul R R' M N] (r : R') (m : M) (n : N) : (r • m) otimesₜ n = m otimesₜ[R] (r • n)
· 使用定理 `TensorProduct.CompatibleSMul.isScalarTower`：∀ {R : Type u_1} {R' : Type 
u_4} [inst : CommSemiring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8} 
  [inst_2 : AddCommMonoid M] [in…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.tmul_smul`：tmul_smul [DistribMulAction R' N] [CompatibleSM
ul R R' M N] (r : R') (x : M) (y : N) : x otimesₜ (r • y) = r • x otimesₜ[R] y
· 使用定理 `RingHomCompTriple.comp_apply`：comp_apply [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
 {x : R₁} : σ₂₃ (σ₁₂ x) = σ₁₃ x
· 使用定理 `Algebra.smul_mul_assoc`：∀ {R : Type u} {A : Type w} [inst : CommSemiring
 R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (r : R) (x y : A),   r • x * y 
= r • (x * y…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `TensorProduct.smul_tmul'`：smul_tmul' (r : R') (m : M) (n : N) : r • m ot
imesₜ[R] n = (r • m) otimesₜ n
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
-/
lemma SurjectiveOnStalks.baseChange
    [Algebra R T] [Algebra R S]
    (hf : (algebraMap R T).SurjectiveOnStalks) :
    (algebraMap S (S ⊗[R] T)).SurjectiveOnStalks := by
  let g : T →+* S ⊗[R] T := Algebra.TensorProduct.includeRight.toRingHom
  intro J hJ
  rw [surjective_localRingHom_iff]
  intro x
  obtain ⟨t, r, a, ht, e⟩ := hf.exists_mul_eq_tmul x (J.comap g) inferInstance
  refine ⟨a, algebraMap _ _ r, 1 ⊗ₜ (r • t), ht, ?_, ?_⟩
  · intro H
    simp only [Algebra.algebraMap_eq_smul_one (A := S), Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_self, id_apply, smul_tmul, ← Algebra.algebraMap_eq_smul_one (A := T)] at H
    rw [Ideal.mem_comap, Algebra.smul_def, g.map_mul] at ht
    exact ht (J.mul_mem_right _ H)
  · simp only [tmul_smul, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
      RingHomCompTriple.comp_apply, Algebra.smul_mul_assoc, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul, mul_one, id_apply, ← e]
    rw [Algebra.algebraMap_eq_smul_one, ← smul_tmul', smul_mul_assoc]
/-
**RingHom.SurjectiveOnStalks.baseChange'** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.Surj
ectiveOnStalks`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {S : Type u_2} [inst_1 : CommRing S] 
{T : Type u_3} [inst_2 : CommRing T]   [inst_3 : Algebra R T] [inst_4 : Algebra 
R S],   (algebraMap R S).SurjectiveOnStalks → Algebra.TensorProduct.includeRight
.SurjectiveOnStalks
参数：algebraMap R S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.SurjectiveOnStalks.comp`：∀ {R : Type u_1} [inst : CommRing R] {S
 : Type u_2} [inst_1 : CommRing S] {T : Type u_3} [inst_2 : CommRing T]   {g : S
 →+* T} {f : R →+* S}…
· 使用引理 `RingHom.surjectiveOnStalks_of_surjective`：surjectiveOnStalks_of_surjecti
ve (h : Function.Surjective f) : SurjectiveOnStalks f
· 使用定理 `AlgEquiv.surjective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [in
st : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : A
lgebra R …
· 使用定理 `RingHom.SurjectiveOnStalks.baseChange`：∀ {R : Type u_1} [inst : CommRing
 R] {S : Type u_2} [inst_1 : CommRing S] {T : Type u_3} [inst_2 : CommRing T]   
[inst_3 : Algebra R T] [ins…
-/
lemma SurjectiveOnStalks.baseChange' [Algebra R T] [Algebra R S]
    (hf : (algebraMap R S).SurjectiveOnStalks) :
    (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := T)).SurjectiveOnStalks := by
  convert!
    (surjectiveOnStalks_of_surjective (Algebra.TensorProduct.comm R T S).surjective).comp
      (hf.baseChange (S := T))
        -- Subsumed by `RingHom.SurjectiveOnStalks.tensorProductMap`.


-- Subsumed by `RingHom.SurjectiveOnStalks.tensorProductMap`.
/-
**RingHom.SurjectiveOnStalks.tensorProductMap_id** 是 Mathlib 中的一个引理，位于命名空间 `Ring
Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma SurjectiveOnStalks.tensorProductMap_id
    {S' : Type*} [CommRing S'] [Algebra R S] [Algebra R T] [Algebra R S']
    {f : S →ₐ[R] S'} (Hf : f.SurjectiveOnStalks) :
    (Algebra.TensorProduct.map f (AlgHom.id R T)).SurjectiveOnStalks := by
  let := f.toRingHom.toAlgebra
  have := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  change (Algebra.TensorProduct.map (Algebra.ofId S S') (AlgHom.id R T)).SurjectiveOnStalks
  convert_to ((Algebra.TensorProduct.cancelBaseChange R S S S' T).toAlgHom.comp
    Algebra.TensorProduct.includeRight).SurjectiveOnStalks
  · congr; ext; simp
  exact (Algebra.TensorProduct.cancelBaseChange R S S S' T).toRingEquiv.surjectiveOnStalks.comp
    Hf.baseChange'
/-
**RingHom.SurjectiveOnStalks.tensorProductMap** 是 Mathlib 中的一个定理，位于命名空间 `RingHom
.SurjectiveOnStalks`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {S : Type u_2} [inst_1 : CommRing S] 
{T : Type u_3} [inst_2 : CommRing T]   {S' : Type u_4} {T' : Type u_5} [inst_3 :
 CommRing S'] [inst_4 : CommRing T'] [inst_5 : Algebra R S]   [inst_6 : Algebra 
R T] [inst_7 : Algebra R S'] [inst_8 : Algebra R T'] {f : S →ₐ[R] S'},   f.Surje
ctiveOnStalks → ∀ {g : T →ₐ[R] T'}, g.SurjectiveOnStalks → (Algebra.TensorProduc
t.map f g).SurjectiveOnStalks
参数：Algebra.TensorProduct.map f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Algebra.TensorProduct.ext`：ext ⦃f g : (A otimes[R] B) ->ₐ[S] C⦄ (ha : f.
comp includeLeft = g.comp includeLeft) (hb : (f.restrictScalars R).comp includeR
ight = (g.restr…
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.TensorProduct.map_comp_includeLeft`：map_comp_includeLeft (f : A 
->ₐ[S] C) (g : B ->ₐ[R] D) : (map f g).comp includeLeft = includeLeft.comp f
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Algebra.TensorProduct.map_restrictScalars_comp_includeRight`：map_restric
tScalars_comp_includeRight (f : A ->ₐ[S] C) (g : B ->ₐ[R] D) : ((map f g).restri
ctScalars R).comp includeRight = includeRight.com…
· 使用定理 `RingHom.SurjectiveOnStalks.comp`：∀ {R : Type u_1} [inst : CommRing R] {S
 : Type u_2} [inst_1 : CommRing S] {T : Type u_3} [inst_2 : CommRing T]   {g : S
 →+* T} {f : R →+* S}…
· 使用定理 `_private.Mathlib.RingTheory.SurjectiveOnStalks.0.RingHom.SurjectiveOnSta
lks.tensorProductMap_id`：∀ {R : Type u_1} [inst : CommRing R] {S : Type u_2} [in
st_1 : CommRing S] {T : Type u_3} [inst_2 : CommRing T]   {S' : Type u_4} [inst_
3 : C…
· 使用定理 `RingEquiv.surjectiveOnStalks`：∀ {R : Type u_1} [inst : CommRing R] {S : 
Type u_2} [inst_1 : CommRing S] (e : R ≃+* S), e.toRingHom.SurjectiveOnStalks
-/
lemma SurjectiveOnStalks.tensorProductMap
    {S' T' : Type*} [CommRing S'] [CommRing T']
    [Algebra R S] [Algebra R T] [Algebra R S'] [Algebra R T']
    {f : S →ₐ[R] S'} (Hf : f.SurjectiveOnStalks) {g : T →ₐ[R] T'} (Hg : g.SurjectiveOnStalks) :
    (Algebra.TensorProduct.map f g).SurjectiveOnStalks := by
  convert!
    RingHom.SurjectiveOnStalks.tensorProductMap_id (T := T') Hf |>.comp <|
      (Algebra.TensorProduct.comm _ _ _).toRingEquiv.surjectiveOnStalks |>.comp <|
        RingHom.SurjectiveOnStalks.tensorProductMap_id (T := S) Hg |>.comp <|
          (Algebra.TensorProduct.comm _ _ _).toRingEquiv.surjectiveOnStalks
  simp only [AlgHom.toRingHom_eq_coe, RingEquiv.toRingHom_eq_coe,
    AlgEquiv.toRingEquiv_toRingHom, ← AlgEquiv.toAlgHom_toRingHom, ← AlgHom.comp_toRingHom]
  congr
  ext <;> simp
/-
**RingHom.surjectiveOnStalks_iff_of_isLocalHom** 是 Mathlib 中的一个引理，位于命名空间 `RingHo
m`。
形式化陈述：surjectiveOnStalks_iff_of_isLocalHom [IsLocalRing S] [IsLocalHom f] : f.Su
rjectiveOnStalks ↔ Function.Surjective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.IsPrime.comap`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : 
Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f : F)   {K : Ideal 
S} [inst_…
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `IsLocalRing.maximalIdeal.isMaximal`：∀ (R : Type u_1) [inst : CommSemirin
g R] [inst_1 : IsLocalRing R], (IsLocalRing.maximalIdeal R).IsMaximal
· 使用引理 `RingHom.surjective_localRingHom_iff`：surjective_localRingHom_iff (P : Id
eal S) [P.IsPrime] : Function.Surjective (Localization.localRingHom _ P f rfl) ↔
 forall s : S, exists x r…
· 使用定理 `isUnit_of_map_unit`：∀ {R : Type u_2} {S : Type u_3} {F : Type u_5} [inst
 : Monoid R] [inst_1 : Monoid S] [inst_2 : FunLike F R S] (f : F)   [IsLocalHom 
f] (a : …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsUnit.mul_right_injective`：∀ {M : Type u_1} [inst : Monoid M] {a : M}, 
IsUnit a → Function.Injective fun x => a * x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsUnit.mul_val_inv`：mul_val_inv (h : IsUnit a) : a * ↑h.unit⁻¹ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `RingHom.surjectiveOnStalks_of_surjective`：surjectiveOnStalks_of_surjecti
ve (h : Function.Surjective f) : SurjectiveOnStalks f
-/
lemma surjectiveOnStalks_iff_of_isLocalHom [IsLocalRing S] [IsLocalHom f] :
    f.SurjectiveOnStalks ↔ Function.Surjective f := by
  refine ⟨fun H x ↦ ?_, fun h ↦ surjectiveOnStalks_of_surjective h⟩
  obtain ⟨y, r, c, hc, hr, e⟩ :=
    (surjective_localRingHom_iff _).mp (H (IsLocalRing.maximalIdeal _) inferInstance) x
  simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hc hr
  refine ⟨(isUnit_of_map_unit f r hr).unit⁻¹ * y, ?_⟩
  apply hr.mul_right_injective
  apply hc.mul_right_injective
  simp only [← map_mul, ← mul_assoc, IsUnit.mul_val_inv, one_mul, e]

end RingHom

