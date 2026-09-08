/-
Copyright (c) 2025 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang
-/
module

public import Mathlib.RingTheory.WittVector.Domain
public import Mathlib.RingTheory.WittVector.Truncated
public import Mathlib.RingTheory.WittVector.Teichmuller
public import Mathlib.RingTheory.AdicCompletion.Basic

/-!
# The ring of Witt vectors is p-torsion free and p-adically complete

In this file, we prove that the ring of Witt vectors `𝕎 k` is p-torsion free and p-adically complete
when `k` is a perfect ring of characteristic `p`.

## Main declarations

* `WittVector.eq_zero_of_p_mul_eq_zero` : If `k` is a perfect ring of characteristic `p`,
  then the Witt vector `𝕎 k` is `p`-torsion free.
* `isAdicCompleteIdealSpanP` : If `k` is a perfect ring of characteristic `p`,
  then the Witt vector `𝕎 k` is `p`-adically complete.
-/

@[expose] public section

namespace WittVector

variable {p : ℕ} [hp : Fact (Nat.Prime p)] {k : Type*} [CommRing k]

local notation "𝕎" => WittVector p

/-
**WittVector.le_coeff_eq_iff_le_sub_coeff_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Wit
tVector`。
形式化陈述：le_coeff_eq_iff_le_sub_coeff_eq_zero {x y : 𝕎 k} {n : Nat} : (forall i < n
, x.coeff i = y.coeff i) ↔ forall i < n, (x - y).coeff i = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TruncatedWittVector.ext`：ext {x y : TruncatedWittVector p n R} (h : fora
ll i, x.coeff i = y.coeff i) : x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WittVector.coeff_truncate`：coeff_truncate (x : 𝕎 R) (i : Fin n) : (trunc
ate n x).coeff i = x.coeff i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem le_coeff_eq_iff_le_sub_coeff_eq_zero {x y : 𝕎 k} {n : ℕ} :
    (∀ i < n, x.coeff i = y.coeff i) ↔ ∀ i < n, (x - y).coeff i = 0 := by
  calc
  _ ↔ x.truncate n = y.truncate n := by
    refine ⟨fun h => ?_, fun h i hi => ?_⟩
    · ext i
      simp [h i]
    · rw [← coeff_truncate x ⟨i, hi⟩, ← coeff_truncate y ⟨i, hi⟩, h]
  _ ↔ (x - y).truncate n = 0 := by
    simp only [map_sub, sub_eq_zero]
  _ ↔ _ := by simp only [← mem_ker_truncate, RingHom.mem_ker]

section PerfectRing

variable [CharP k p] [PerfectRing k p]

/--
If `k` is a perfect ring of characteristic `p`, then the ring of Witt vectors `𝕎 k` is
`p`-torsion free.
-/
/-
**WittVector.eq_zero_of_p_mul_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：eq_zero_of_p_mul_eq_zero (x : 𝕎 k) (h : x * p = 0) : x = 0
参数：x : 𝕎 k；h : x * p = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_eq_zero_iff`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : 
Zero M] [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F
), Fu…
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `WittVector.verschiebung_injective`：verschiebung_injective : Function.Inj
ective (verschiebung : 𝕎 R -> 𝕎 R)
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `WittVector.frobenius_bijective`：frobenius_bijective [PerfectRing R p] : 
Function.Bijective (@WittVector.frobenius p R _ _)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WittVector.frobenius_verschiebung`：frobenius_verschiebung (x : 𝕎 R) : fr
obenius (verschiebung x) = x * p

--- 原说明 ---
If `k` is a perfect ring of characteristic `p`, then the ring of Witt vectors `𝕎
 k` is
`p`-torsion free.
-/
theorem eq_zero_of_p_mul_eq_zero (x : 𝕎 k) (h : x * p = 0) : x = 0 := by
  rwa [← frobenius_verschiebung, _root_.map_eq_zero_iff _ (frobenius_bijective p k).injective,
      _root_.map_eq_zero_iff _ (verschiebung_injective p k)] at h

/--
If `k` is a perfect ring of characteristic `p`, a Witt vector `x : 𝕎 k` falls in ideal generated by
`p` if and only if its zeroth coefficient is `0`.
-/
/-
**WittVector.mem_span_p_iff_coeff_zero_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `WittVe
ctor`。
形式化陈述：mem_span_p_iff_coeff_zero_eq_zero (x : 𝕎 k) : x in (Ideal.span {(p : 𝕎 k)}
) ↔ x.coeff 0 = 0
参数：x : 𝕎 k。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `WittVector.mul_charP_coeff_zero`：mul_charP_coeff_zero [CharP R p] (x : 𝕎
 R) : (x * p).coeff 0 = 0
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Function.iterate_one`：iterate_one : f^[1] = f
· 使用定理 `WittVector.eq_iterate_verschiebung`：eq_iterate_verschiebung {x : 𝕎 R} {n
 : Nat} (h : forall i < n, x.coeff i = 0) : x = verschiebung^[n] (x.shift n)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WittVector.verschiebung_frobenius`：verschiebung_frobenius [CharP R p] (x
 : 𝕎 R) : verschiebung (frobenius x) = x * p
· 使用定理 `WittVector.frobeniusEquiv_apply`：∀ (p : ℕ) (R : Type u_1) [hp : Fact (Na
t.Prime p)] [inst : CommRing R] [inst_1 : CharP R p] [inst_2 : PerfectRing R p],
   ⇑(WittVector.frobe…
· 使用定理 `RingEquiv.apply_symm_apply`：apply_symm_apply (e : R ≃+* S) : forall x, e
 (e.symm x) = x

--- 原说明 ---
If `k` is a perfect ring of characteristic `p`, a Witt vector `x : 𝕎 k` falls in
 ideal generated by
`p` if and only if its zeroth coefficient is `0`.
-/
theorem mem_span_p_iff_coeff_zero_eq_zero (x : 𝕎 k) :
    x ∈ (Ideal.span {(p : 𝕎 k)}) ↔ x.coeff 0 = 0 := by
  simp_rw [Ideal.mem_span_singleton, dvd_def, mul_comm]
  refine ⟨fun ⟨u, hu⟩ ↦ ?_, fun h ↦ ?_⟩
  · rw [hu, mul_charP_coeff_zero]
  · use (frobeniusEquiv p k).symm (x.shift 1)
    calc
    _ = verschiebung (x.shift 1) := by
      simpa using eq_iterate_verschiebung (n := 1) (by simp [h])
    _ = _ := by
      rw [← verschiebung_frobenius, ← frobeniusEquiv_apply,
          RingEquiv.apply_symm_apply (frobeniusEquiv p k) _]

/--
If `k` is a perfect ring of characteristic `p`, a Witt vector `x : 𝕎 k` falls in ideal generated by
`p ^ n` if and only if its initial `n` coefficients are `0`.
-/
/-
**WittVector.mem_span_p_pow_iff_le_coeff_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Witt
Vector`。
形式化陈述：mem_span_p_pow_iff_le_coeff_eq_zero (x : 𝕎 k) (n : Nat) : x in (Ideal.span
 {(p ^ n : 𝕎 k)}) ↔ forall m, m < n -> x.coeff m = 0
参数：x : 𝕎 k；n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `WittVector.mul_pow_charP_coeff_zero`：mul_pow_charP_coeff_zero [CharP R p
] (x : 𝕎 R) {m n : Nat} (h : m < n) : (x * p ^ n).coeff m = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WittVector.iterate_verschiebung_iterate_frobenius`：iterate_verschiebung_
iterate_frobenius (x : 𝕎 R) (n : Nat) : verschiebung^[n] (frobenius^[n] x) = x *
 (p ^ n)
· 使用定理 `WittVector.eq_iterate_verschiebung`：eq_iterate_verschiebung {x : 𝕎 R} {n
 : Nat} (h : forall i < n, x.coeff i = 0) : x = verschiebung^[n] (x.shift n)
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `Function.Commute.comp_iterate`：comp_iterate (h : Commute f g) (n : Nat) 
: (f ∘ g)^[n] = f^[n] ∘ g^[n]
· 使用定理 `Function.Commute.eq_1`：∀ {α : Type u_1} (f g : α → α), Function.Commute 
f g = Function.Semiconj f g g
· 使用定理 `Function.Semiconj.eq_1`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (ga 
: α → α) (gb : β → β),   Function.Semiconj f ga gb = ∀ (x : α), f (ga x) = gb (f
 x)
· 使用定理 `WittVector.frobeniusEquiv_apply`：∀ (p : ℕ) (R : Type u_1) [hp : Fact (Na
t.Prime p)] [inst : CommRing R] [inst_1 : CharP R p] [inst_2 : PerfectRing R p],
   ⇑(WittVector.frobe…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RingEquiv.apply_symm_apply`：apply_symm_apply (e : R ≃+* S) : forall x, e
 (e.symm x) = x
· 使用定理 `RingEquiv.symm_apply_apply`：symm_apply_apply (e : R ≃+* S) : forall x, e
.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `RingEquiv.coe_trans`：coe_trans (e₁ : R ≃+* S) (e₂ : S ≃+* S') : (e₁.tran
s e₂ : R -> S') = e₂ ∘ e₁
· 使用定理 `RingEquiv.symm_trans_self`：symm_trans_self (e : R ≃+* S) : e.symm.trans 
e = RingEquiv.refl S
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Function.iterate_id`：iterate_id (n : Nat) : (id : α -> α)^[n] = id

--- 原说明 ---
If `k` is a perfect ring of characteristic `p`, a Witt vector `x : 𝕎 k` falls in
 ideal generated by
`p ^ n` if and only if its initial `n` coefficients are `0`.
-/
theorem mem_span_p_pow_iff_le_coeff_eq_zero (x : 𝕎 k) (n : ℕ) :
    x ∈ (Ideal.span {(p ^ n : 𝕎 k)}) ↔ ∀ m, m < n → x.coeff m = 0 := by
  simp_rw [Ideal.mem_span_singleton, dvd_def, mul_comm]
  refine ⟨fun ⟨u, hu⟩ m hm ↦ ?_, fun h ↦ ?_⟩
  · rw [hu, mul_pow_charP_coeff_zero _ hm]
  · use (frobeniusEquiv p k).symm^[n] (x.shift n)
    rw [← iterate_verschiebung_iterate_frobenius]
    calc
    _ = verschiebung^[n] (x.shift n) := by
      simpa using eq_iterate_verschiebung (x := x) (n := n) h
    _ = _ := by
      congr
      rw [← Function.comp_apply (f := frobenius^[n]), ← Function.Commute.comp_iterate]
      · rw [← WittVector.frobeniusEquiv_apply, ← RingEquiv.coe_trans]
        simp
      · rw [Function.Commute, Function.Semiconj, ← WittVector.frobeniusEquiv_apply]
        simp only [RingEquiv.apply_symm_apply, RingEquiv.symm_apply_apply, implies_true]
/-
**WittVector.ker_constantCoeff** 是 Mathlib 中的一个引理，位于命名空间 `WittVector`。
形式化陈述：ker_constantCoeff : RingHom.ker constantCoeff = Ideal.span {(p : 𝕎 k)}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `WittVector.constantCoeff_apply`：∀ {p : ℕ} {R : Type u_1} [inst : CommRin
g R] [inst_1 : Fact (Nat.Prime p)] (x : WittVector p R),   WittVector.constantCo
eff x = x.coeff 0
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma ker_constantCoeff : RingHom.ker constantCoeff = Ideal.span {(p : 𝕎 k)} := by
  ext
  simp [mem_span_p_iff_coeff_zero_eq_zero]

/-- If `k` is a perfect ring of characteristic `p`, there is an isomorphism between the quotient
`𝕎 k / p` and `k`.
-/
/-
**WittVector.quotientPEquiv** 是 Mathlib 中的一个定义，位于命名空间 `WittVector`。
形式化陈述：quotientPEquiv : 𝕎 k ⧸ Ideal.span {(p : 𝕎 k)} ≃+* k
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `WittVector.constantCoeff_surjective`：constantCoeff_surjective : Function
.Surjective (constantCoeff : 𝕎 R -> R)

--- 原说明 ---
If `k` is a perfect ring of characteristic `p`, there is an isomorphism between 
the quotient
`𝕎 k / p` and `k`.
-/
noncomputable def quotientPEquiv : 𝕎 k ⧸ Ideal.span {(p : 𝕎 k)} ≃+* k :=
  (Ideal.quotEquivOfEq ker_constantCoeff.symm).trans
    (RingHom.quotientKerEquivOfSurjective (constantCoeff_surjective p))

@[simp]
/-
**WittVector.quotientPEquiv_mk** 是 Mathlib 中的一个引理，位于命名空间 `WittVector`。
形式化陈述：quotientPEquiv_mk (x : 𝕎 k) : quotientPEquiv (Quot.mk _ x) = constantCoeff
 x
参数：x : 𝕎 k。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma quotientPEquiv_mk (x : 𝕎 k) : quotientPEquiv (Quot.mk _ x) = constantCoeff x := rfl

/--
If `k` is a perfect ring of characteristic `p`, then the ring of Witt vectors `𝕎 k`
is `p`-adically complete.
-/
/-
**WittVector.isAdicCompleteIdealSpanP** 是 Mathlib 中的一个实例，位于命名空间 `WittVector`。
形式化陈述：isAdicCompleteIdealSpanP : IsAdicComplete (Ideal.span {(p : 𝕎 k)}) (𝕎 k) w
here haus'
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `WittVector.ext`：ext {x y : 𝕎 R} (h : forall n, x.coeff n = y.coeff n) : 
x = y
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.mul_top`：mul_top [I.IsTwoSided] : I * ⊤ = I
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `WittVector.zero_coeff`：zero_coeff (n : Nat) : (0 : 𝕎 R).coeff n = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Ideal.span_singleton_pow`：span_singleton_pow (s : R) [(span {s}).IsTwoSi
ded] (n : Nat) : span {s} ^ n = (span {s ^ n} : Ideal R)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ

--- 原说明 ---
If `k` is a perfect ring of characteristic `p`, then the ring of Witt vectors `𝕎
 k`
is `p`-adically complete.
-/
instance isAdicCompleteIdealSpanP : IsAdicComplete (Ideal.span {(p : 𝕎 k)}) (𝕎 k) where
  haus' := by
    intro _ h
    ext n
    simp only [smul_eq_mul, Ideal.mul_top] at h
    have := h (n + 1)
    simp only [Ideal.span_singleton_pow, SModEq.zero,
        mem_span_p_pow_iff_le_coeff_eq_zero] at this
    simpa using this n
  prec' := by
    intro x h
    -- construct the limit Witt vector w diagonally
    use .mk p (fun n ↦ (x (n + 1)).coeff n)
    intro n
    simp only [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, SModEq.sub_mem,
      mem_span_p_pow_iff_le_coeff_eq_zero, ← le_coeff_eq_iff_le_sub_coeff_eq_zero] at h ⊢
    intro i hi
    exact (h hi i (Nat.lt_succ_self i)).symm

end PerfectRing

end WittVector

