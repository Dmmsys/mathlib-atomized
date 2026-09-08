/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Eric Wieser
-/
module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Nonunits
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# Characteristic of quotient rings
-/

public section

/-
**CharP.ker_intAlgebraMap_eq_span** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CharP.ker_intAlgebraMap_eq_span {R : Type*} [Ring R] (p : Nat) [CharP R p]
 : RingHom.ker (algebraMap Int R) = Ideal.span {(p : Int)}
参数：p : Nat。
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
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用引理 `CharP.intCast_eq_zero_iff`：intCast_eq_zero_iff (a : Int) : (a : R) = 0 ↔
 (p : Int) ∣ a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem CharP.ker_intAlgebraMap_eq_span
    {R : Type*} [Ring R] (p : ℕ) [CharP R p] :
    RingHom.ker (algebraMap ℤ R) = Ideal.span {(p : ℤ)} := by
  ext a
  simp [CharP.intCast_eq_zero_iff R p, Ideal.mem_span_singleton]

variable {R : Type*} [CommRing R]

namespace CharP

variable (R) in
/-
**CharP.quotient** 是 Mathlib 中的一个定理，位于命名空间 `CharP`。
形式化陈述：quotient (p : Nat) [hp1 : Fact p.Prime] (hp2 : ↑p in nonunits R) : CharP (
R ⧸ (Ideal.span ({(p : R)} : Set R) : Ideal R)) p
参数：p : Nat；hp2 : ↑p in nonunits R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.Quotient.eq_zero_iff_mem`：eq_zero_iff_mem : mk I a = 0 ↔ a in I
· 使用定理 `Ideal.subset_span`：subset_span {s : Set α} : s subseteq span s
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用引理 `ringChar.of_eq`：of_eq {p : Nat} (h : ringChar R = p) : CharP R p
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.dvd_prime`：dvd_prime {p m : Nat} (pp : Prime p) : m ∣ p ↔ m = 1 ∨ m 
= p
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用引理 `ringChar.dvd`：dvd {x : Nat} (hx : (x : R) = 0) : ringChar R ∣ x
· 使用定理 `isUnit_iff_dvd_one`：isUnit_iff_dvd_one {x : α} : IsUnit x ↔ x ∣ 1
· 使用定理 `Ideal.mem_span_singleton`：mem_span_singleton {x y : α} : x in span ({y} 
: Set α) ↔ y ∣ x
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `CharP.CharOne.subsingleton`：∀ {R : Type u_1} [inst : NonAssocSemiring R]
 [CharP R 1], Subsingleton R
-/
theorem quotient (p : ℕ) [hp1 : Fact p.Prime] (hp2 : ↑p ∈ nonunits R) :
    CharP (R ⧸ (Ideal.span ({(p : R)} : Set R) : Ideal R)) p :=
  have hp0 : (p : R ⧸ (Ideal.span {(p : R)} : Ideal R)) = 0 :=
    map_natCast (Ideal.Quotient.mk (Ideal.span {(p : R)} : Ideal R)) p ▸
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span <| Set.mem_singleton _)
  ringChar.of_eq <|
    Or.resolve_left ((Nat.dvd_prime hp1.1).1 <| ringChar.dvd hp0) fun h1 =>
      hp2 <|
        isUnit_iff_dvd_one.2 <|
          Ideal.mem_span_singleton.1 <|
            Ideal.Quotient.eq_zero_iff_mem.1 <|
              @Subsingleton.elim _ (@CharOne.subsingleton _ _ (ringChar.of_eq h1)) _ _

/-- If an ideal does not contain any coercions of natural numbers other than zero, then its quotient
inherits the characteristic of the underlying ring. -/
/-
**CharP.quotient'** 是 Mathlib 中的一个定理，位于命名空间 `CharP`。
形式化陈述：quotient' (p : Nat) [CharP R p] (I : Ideal R) (h : forall x : Nat, (x : R)
 in I -> (x : R) = 0) : CharP (R ⧸ I) p where cast_eq_zero_iff x
参数：p : Nat；I : Ideal R；h : forall x : Nat, (x : R) in I -> (x : R) = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CharP.cast_eq_zero_iff`：∀ (R : Type u_2) {inst : AddMonoidWithOne R} (p 
: outParam ℕ) [self : CharP R p] (x : ℕ), ↑x = 0 ↔ p ∣ x
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Ideal.Quotient.eq`：∀ {R : Type u} [inst : Ring R] {I : Ideal R} {x y : R
} [inst_1 : I.IsTwoSided],   (Ideal.Quotient.mk I) x = (Ideal.Quotient.mk I) y ↔
 x - y …
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Ideal.zero_mem`：∀ {α : Type u} [inst : Semiring α] (I : Ideal α), 0 ∈ I

--- 原说明 ---
If an ideal does not contain any coercions of natural numbers other than zero, t
hen its quotient
inherits the characteristic of the underlying ring.
-/
theorem quotient' (p : ℕ) [CharP R p] (I : Ideal R) (h : ∀ x : ℕ, (x : R) ∈ I → (x : R) = 0) :
    CharP (R ⧸ I) p where
  cast_eq_zero_iff x := by
    rw [← cast_eq_zero_iff R p x, ← map_natCast (Ideal.Quotient.mk I)]
    refine Ideal.Quotient.eq.trans (?_ : ↑x - 0 ∈ I ↔ _)
    rw [sub_zero]
    exact ⟨h x, fun h' => h'.symm ▸ I.zero_mem⟩

/-- `CharP.quotient'` as an `Iff`. -/
/-
**CharP.quotient_iff** 是 Mathlib 中的一个定理，位于命名空间 `CharP`。
形式化陈述：quotient_iff (n : Nat) [CharP R n] (I : Ideal R) : CharP (R ⧸ I) n ↔ foral
l x : Nat, ↑x in I -> (x : R) = 0
参数：n : Nat；I : Ideal R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CharP.cast_eq_zero_iff`：∀ (R : Type u_2) {inst : AddMonoidWithOne R} (p 
: outParam ℕ) [self : CharP R p] (x : ℕ), ↑x = 0 ↔ p ∣ x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.Quotient.mk_eq_zero`：mk_eq_zero : (mk x : M ⧸ p) = 0 ↔ x in p
· 使用定理 `CharP.quotient'`：quotient' (p : Nat) [CharP R p] (I : Ideal R) (h : fora
ll x : Nat, (x : R) in I -> (x : R) = 0) : CharP (R ⧸ I) p where cast_eq_zero_if
f x

--- 原说明 ---
`CharP.quotient'` as an `Iff`.
-/
theorem quotient_iff (n : ℕ) [CharP R n] (I : Ideal R) :
    CharP (R ⧸ I) n ↔ ∀ x : ℕ, ↑x ∈ I → (x : R) = 0 := by
  refine ⟨fun _ x hx => ?_, CharP.quotient' n I⟩
  rw [CharP.cast_eq_zero_iff R n, ← CharP.cast_eq_zero_iff (R ⧸ I) n _]
  exact (Submodule.Quotient.mk_eq_zero I).mpr hx

/-- `CharP.quotient_iff`, but stated in terms of inclusions of ideals. -/
/-
**CharP.quotient_iff_le_ker_natCast** 是 Mathlib 中的一个定理，位于命名空间 `CharP`。
形式化陈述：quotient_iff_le_ker_natCast (n : Nat) [CharP R n] (I : Ideal R) : CharP (R
 ⧸ I) n ↔ I.comap (Nat.castRingHom R) <= RingHom.ker (Nat.castRingHom R)
参数：n : Nat；I : Ideal R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CharP.quotient_iff`：quotient_iff (n : Nat) [CharP R n] (I : Ideal R) : C
harP (R ⧸ I) n ↔ forall x : Nat, ↑x in I -> (x : R) = 0
· 使用定理 `RingHom.ker_eq_comap_bot`：ker_eq_comap_bot (f : F) : ker f = Ideal.comap
 f ⊥
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
`CharP.quotient_iff`, but stated in terms of inclusions of ideals.
-/
theorem quotient_iff_le_ker_natCast (n : ℕ) [CharP R n] (I : Ideal R) :
    CharP (R ⧸ I) n ↔ I.comap (Nat.castRingHom R) ≤ RingHom.ker (Nat.castRingHom R) := by
  rw [CharP.quotient_iff, RingHom.ker_eq_comap_bot]; rfl

end CharP

/-
**Ideal.natCast_mem_of_charP_quotient** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.natCast_mem_of_charP_quotient (p : Nat) (I : Ideal R) [CharP (R ⧸ I)
 p] : (p : R) in I
参数：p : Nat；I : Ideal R；R ⧸ I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.Quotient.eq_zero_iff_mem`：eq_zero_iff_mem : mk I a = 0 ↔ a in I
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Ideal.natCast_mem_of_charP_quotient (p : ℕ) (I : Ideal R) [CharP (R ⧸ I) p] :
    (p : R) ∈ I :=
  Ideal.Quotient.eq_zero_iff_mem.mp <| by simp
/-
**Ideal.Quotient.index_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.Quotient.index_eq_zero (I : Ideal R) : (↑I.toAddSubgroup.index : R ⧸
 I) = 0
参数：I : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddSubgroup.index.eq_1`：∀ {G : Type u_1} [inst : AddGroup G] (H : AddSub
group G), H.index = Nat.card (G ⧸ H)
· 使用定理 `Nat.card_eq`：Nat.card_eq (α : Type*) : Nat.card α = if _ : Finite α then
 @Fintype.card α (Fintype.ofFinite α) else 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用引理 `Nat.cast_card_eq_zero`：Nat.cast_card_eq_zero (R) [AddGroupWithOne R] [Fi
ntype R] : (Fintype.card R : R) = 0
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Ideal.Quotient.index_eq_zero (I : Ideal R) : (↑I.toAddSubgroup.index : R ⧸ I) = 0 := by
  rw [AddSubgroup.index, Nat.card_eq]
  split_ifs with hq; swap
  · simp
  let : Fintype (R ⧸ I) := @Fintype.ofFinite _ hq
  exact Nat.cast_card_eq_zero (R ⧸ I)
